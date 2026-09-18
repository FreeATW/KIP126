/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Bounded extension spectral sequence: basic convergence, filtered crossing.
Reference: extension.tex (wangguozhen-fudan/spectral-sequence-notes)
-/

import KIPBase.SpectralSequence.Basic
import KIPBase.SpectralSequence.Convergence
import KIPBase.SpectralSequence.FilteredComplex
import KIPBase.SpectralSequence.Crossing

universe u v w

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Two-term complex helpers

The extension spectral sequence is built from a two-term filtered complex
`A₁(t) →[aMap t] A₂(t)` for each stem degree `t`. These helpers define the
graded object, differential, and filtration for such a complex. -/

/-- The graded object for a two-term complex: `A(1) = X₁`, `A(0) = X₂`,
    `A(k) = 0` for all other `k`. The zero object is `⊥_ C` (initial object
    in an abelian category). -/
noncomputable def twoTermObj (X₁ X₂ : C) : ℤ → C := fun k =>
  if k = 1 then X₁ else if k = 0 then X₂ else ⊥_ C

@[simp] lemma twoTermObj_one (X₁ X₂ : C) : twoTermObj X₁ X₂ 1 = X₁ := by
  simp [twoTermObj]

@[simp] lemma twoTermObj_zero' (X₁ X₂ : C) : twoTermObj X₁ X₂ 0 = X₂ := by
  simp [twoTermObj]

lemma twoTermObj_other (X₁ X₂ : C) (k : ℤ) (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    twoTermObj X₁ X₂ k = ⊥_ C := by
  simp [twoTermObj, h₁, h₀]

/-- The differential for the two-term complex: `d(1) = f : X₁ ⟶ X₂`,
    `d(k) = 0` for `k ≠ 1`. Uses `eqToHom` to bridge the definitional
    gap between `twoTermObj` at specific integers. -/
noncomputable def twoTermDiff (X₁ X₂ : C) (f : X₁ ⟶ X₂) :
    (k : ℤ) → twoTermObj X₁ X₂ k ⟶ twoTermObj X₁ X₂ (k - 1) := fun k =>
  if h : k = 1 then
    eqToHom (show twoTermObj X₁ X₂ k = X₁ by simp [twoTermObj, h]) ≫ f ≫
      eqToHom (show X₂ = twoTermObj X₁ X₂ (k - 1) by simp [twoTermObj, h])
  else 0

theorem twoTermDiff_sq (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    twoTermDiff X₁ X₂ f k ≫ twoTermDiff X₁ X₂ f (k - 1) = 0 := by
  simp only [twoTermDiff]
  by_cases h : k = 1
  · subst h; simp
  · simp [h]

/-- The filtration for the two-term complex: at `k = 1` use `fil₁`,
    at `k = 0` use `fil₂`, at all other `k` use `⊤` (which equals `⊥`
    on the zero object). -/
noncomputable def twoTermFil {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) :
    ℤ → (k : ℤ) → Subobject (twoTermObj X₁ X₂ k) := fun s k =>
  if h₁ : k = 1 then h₁ ▸ fil₁ s
  else if h₀ : k = 0 then h₀ ▸ fil₂ s
  else ⊤

@[simp] lemma twoTermFil_one {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 1 = fil₁ s := by simp [twoTermFil]

@[simp] lemma twoTermFil_zero' {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 0 = fil₂ s := by simp [twoTermFil]

private lemma subobject_eq_bot_of_isZero {X : C} (hX : IsZero X) (P : Subobject X) : P = ⊥ := by
  have hP_zero : IsZero (Subobject.underlying.obj P) := hX.of_mono P.arrow
  apply le_antisymm
  · apply Subobject.le_of_comm (hP_zero.to_ _)
    apply hX.eq_of_tgt
  · exact bot_le

private lemma subobject_top_eq_bot_of_isInitial :
    (⊤ : Subobject (⊥_ C)) = ⊥ :=
  subobject_eq_bot_of_isZero (by apply IsInitial.isZero; exact initialIsInitial) ⊤

/-! ### Underlying filtered complex

Given a convergence morphism `cm : ConvergenceMorphism conv₁ conv₂` with
`cm.aMap : A₁ k' ⟶ A₂ k'`, for each stem degree `t : ω'` we build a
`FilteredComplex C` whose underlying chain complex is the two-term complex
`A₁(t) →[cm.aMap t] A₂(t)`, with filtration inherited from `F₁` and `F₂`. -/

variable {ω' : Type w}

/-- The two-term filtered complex `A₁(t) → A₂(t)` at stem degree `t`,
    with filtration inherited from `F₁` and `F₂`. -/
noncomputable def underlyingComplex
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
             Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') : FilteredComplex C where
  A := twoTermObj (A₁ t) (A₂ t)
  d := twoTermDiff (A₁ t) (A₂ t) (aMap t)
  d_comp_d := twoTermDiff_sq (A₁ t) (A₂ t) (aMap t)
  fil := twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t)
  fil_anti := fun s k => by
    simp only [twoTermFil]
    by_cases h₁ : k = 1
    · subst h₁; simp only [↓reduceDIte]; exact F₁.mono s t
    · by_cases h₀ : k = 0
      · subst h₀; simp only [↓reduceDIte, h₁]; exact F₂.mono s t
      · simp [h₁, h₀]
  d_preserves_fil := fun s k => by
    by_cases h : k = 1
    · subst h
      obtain ⟨φ, hφ⟩ := hcompat s t
      have h1 : twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s 1 = F₁.F s t :=
        by simp [twoTermFil]
      have h0 : twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s (1 - 1) = F₂.F s t :=
        by simp [twoTermFil]
      have harr0 : (twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s (1 - 1)).arrow =
          eqToHom (by simp [twoTermFil, twoTermObj]) ≫ (F₂.F s t).arrow := by
        simp [twoTermFil, twoTermObj]
      have harr1 : (twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s 1).arrow =
          eqToHom (by simp [twoTermFil, twoTermObj]) ≫ (F₁.F s t).arrow := by
        simp [twoTermFil, twoTermObj]
      exact ⟨h1 ▸ h0 ▸ φ, by
        simp only [twoTermDiff, ↓reduceDIte, harr0, harr1,
          eqToHom_refl, Category.id_comp, Category.comp_id]
        exact hφ⟩
    · exact ⟨0, by simp [twoTermDiff, h]⟩

/-- The filtration on the two-term complex is bounded when the convergence
    filtrations `F₁` and `F₂` are bounded. -/
noncomputable def underlyingComplexBounded
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
             Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω')
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) :
    (underlyingComplex aMap hcompat t).IsBounded where
  lo := fun k =>
    if k = 1 then bnd₁.lo t else if k = 0 then bnd₂.lo t else 0
  hi := fun k =>
    if k = 1 then bnd₁.hi t else if k = 0 then bnd₂.hi t else 0
  lo_le_hi := fun k => by
    by_cases h₁ : k = 1
    · simp only [h₁, ↓reduceIte]; exact bnd₁.lo_le_hi t
    · by_cases h₀ : k = 0
      · simp only [h₀, ↓reduceIte]; exact bnd₂.lo_le_hi t
      · simp [h₁, h₀]
  boundedBelow := fun k s hs => by
    simp only [underlyingComplex, twoTermFil]
    by_cases h₁ : k = 1
    · subst h₁; simp only [↓reduceDIte] at hs ⊢; exact bnd₁.boundedBelow t s hs
    · by_cases h₀ : k = 0
      · subst h₀; simp only [h₁, ↓reduceDIte] at hs ⊢; exact bnd₂.boundedBelow t s hs
      · simp [h₁, h₀]
  boundedAbove := fun k s hs => by
    simp only [underlyingComplex, twoTermFil]
    by_cases h₁ : k = 1
    · subst h₁; simp only [↓reduceDIte] at hs ⊢; exact bnd₁.boundedAbove t s hs
    · by_cases h₀ : k = 0
      · subst h₀; simp only [h₁, ↓reduceDIte] at hs ⊢; exact bnd₂.boundedAbove t s hs
      · simp only [h₁, h₀] at hs
        have hz : IsZero (twoTermObj (A₁ t) (A₂ t) k) := by
          have : twoTermObj (A₁ t) (A₂ t) k = ⊥_ C := by
            simp [twoTermObj, if_neg h₁, if_neg h₀]
          rw [this]
          apply IsInitial.isZero; exact initialIsInitial
        simp only [dif_neg h₁, dif_neg h₀]
        exact subobject_eq_bot_of_isZero hz ⊤

/-! ### Extension spectral sequence

The extension spectral sequence (ESS) associated to a morphism of converging
spectral sequences. For each stem degree `t`, the ESS is the spectral sequence
of the two-term filtered complex `A₁(t) → A₂(t)`.

The `E₀`-page of the ESS decomposes as `E∞(V₁) ⊕ E∞(V₂)`, and the
differential has only the `E∞(V₁) → E∞(V₂)` component nonzero. -/

variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- The extension spectral sequence data, parameterized by a convergence
    morphism and bounded filtration hypotheses. For each stem degree `t`,
    this produces a spectral sequence indexed by `ℤ × ℤ` via
    `FilteredComplex.toSpectralSequence`. -/
structure BoundedExtensionSS
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (cm : ConvergenceMorphism conv₁ conv₂)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) : Prop where

/-- The underlying two-term filtered complex at each stem degree. -/
noncomputable def BoundedExtensionSS.complex
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') : FilteredComplex C :=
  underlyingComplex cm.aMap cm.filtration_compat t

/-- Boundedness of the underlying complex at each stem. -/
noncomputable def BoundedExtensionSS.bounded
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    (ext.complex t).IsBounded :=
  underlyingComplexBounded cm.aMap cm.filtration_compat t bnd₁ bnd₂

/-- The extension spectral sequence at stem degree `t`:
    the spectral sequence associated to the two-term filtered complex
    `A₁(t) → A₂(t)`. -/
noncomputable def BoundedExtensionSS.ess
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  (ext.complex t).toSpectralSequence (ext.bounded t)

/-- The default `BoundedExtensionSS` instance using the standard construction. -/
noncomputable def BoundedExtensionSS.mk'
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (cm : ConvergenceMorphism conv₁ conv₂)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) :
    BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂ := ⟨⟩

/-- The weak convergence of the extension spectral sequence at stem `t`:
    the ESS converges to the homology of the two-term complex `A₁(t) → A₂(t)`. -/
noncomputable def BoundedExtensionSS.weakConvergence
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    Convergence (ext.ess t)
      (ext.complex t).homologyObj (ext.complex t).homologyFiltration :=
  (ext.complex t).weakConvergence (ext.bounded t)

/-! ### E₀-page structure

The E₀-page of the ESS at bidegree `(s, k)` is the associated graded
`gr^s` of the two-term complex. For `k = 1`, this is `gr^s(A₁) ≅ E∞(V₁)`,
and for `k = 0`, this is `gr^s(A₂) ≅ E∞(V₂)`.

The E₀-page differential only has the `(s, 1) → (s, 0)` component nonzero,
which defines the ESS differential `d₀^f`. -/

/-- The E₀-page of the ESS at `(s, 1)` is the associated graded of
    `A₁(t)` at filtration degree `s`, i.e., `F₁^s / F₁^{s+1}`.
    This equals `E∞^s(V₁)` under the convergence isomorphism. -/
noncomputable def BoundedExtensionSS.e0PageAtOne
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) : C :=
  (ext.complex t).assocGraded s 1

/-- The E₀-page of the ESS at `(s, 0)` is the associated graded of
    `A₂(t)` at filtration degree `s`, i.e., `F₂^s / F₂^{s+1}`.
    This equals `E∞^s(V₂)` under the convergence isomorphism. -/
noncomputable def BoundedExtensionSS.e0PageAtZero
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) : C :=
  (ext.complex t).assocGraded s 0

/-- The E₀-page at `(s, 1)` of the ESS equals the associated graded of
    the `F₁`-filtration on `A₁(t)` at filtration degree `s`. -/
theorem BoundedExtensionSS.e0PageAtOne_eq
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) :
    ext.e0PageAtOne t s = F₁.associatedGraded s t := by
  simp only [e0PageAtOne, BoundedExtensionSS.complex, underlyingComplex, FilteredComplex.assocGraded,
    Filtration.associatedGraded]
  congr 1

/-- The E₀-page at `(s, 0)` of the ESS equals the associated graded of
    the `F₂`-filtration on `A₂(t)` at filtration degree `s`. -/
theorem BoundedExtensionSS.e0PageAtZero_eq
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) :
    ext.e0PageAtZero t s = F₂.associatedGraded s t := by
  simp only [e0PageAtZero, BoundedExtensionSS.complex, underlyingComplex, FilteredComplex.assocGraded,
    Filtration.associatedGraded]
  congr 1

/-- The d₀ differential of the ESS at `(s, 1) → (s, 0)` is the map on
    associated graded pieces induced by `cm.aMap`:
    `gr^s(A₁, t) → gr^s(A₂, t)`. -/
noncomputable def BoundedExtensionSS.d0
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) :
    ext.e0PageAtOne t s ⟶ ext.e0PageAtZero t s :=
  (ext.complex t).assocGradedDiff s 1

/-- `d₀` equals the induced map on associated graded pieces from `cm.aMap`. -/
theorem BoundedExtensionSS.d0_eq_inducedAssocGradedMap
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) :
    ext.d0 t s =
      eqToHom (ext.e0PageAtOne_eq t s) ≫
        Filtration.inducedAssocGradedMap cm.aMap cm.filtration_compat s t ≫
        eqToHom (ext.e0PageAtZero_eq t s).symm := by
  simp only [d0, BoundedExtensionSS.complex]
  set FC := underlyingComplex cm.aMap cm.filtration_compat t with hFC
  change FC.assocGradedDiff s 1 = _
  -- The two-term filtration at k=1,0 agrees with F₁,F₂ (def'ly for Subobjects, prop'ly for ofLE).
  have hofLE1 : Subobject.ofLE (FC.fil (s + 1) 1) (FC.fil s 1) (FC.fil_anti s 1) =
      Subobject.ofLE (F₁.F (s + 1) t) (F₁.F s t) (F₁.mono s t) := by
    simp [FC, underlyingComplex, twoTermFil]
  have hofLE0 : Subobject.ofLE (FC.fil (s + 1) (1 - 1)) (FC.fil s (1 - 1))
      (FC.fil_anti s (1 - 1)) =
      Subobject.ofLE (F₂.F (s + 1) t) (F₂.F s t) (F₂.mono s t) := by
    simp [FC, underlyingComplex, twoTermFil]
  -- Unfold assocGradedDiff to cokernel.desc, then cancel the epi cokernel.π.
  simp only [FilteredComplex.assocGradedDiff, FilteredComplex.assocGraded, id_eq]
  apply (cancel_epi (cokernel.π (Subobject.ofLE (FC.fil (s + 1) 1) (FC.fil s 1)
    (FC.fil_anti s 1)))).mp
  rw [cokernel.π_desc]
  -- Simplify the eqToHom transports (they are identities since twoTermFil reduces def'ly).
  simp only [Filtration.inducedAssocGradedMap,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  -- Unfold cokernel.map to cokernel.desc and use `change` to syntactically unify
  -- the ofLE arguments (definitionally equal but syntactically different).
  unfold cokernel.map
  change (FC.d_preserves_fil s 1).choose ≫
    cokernel.π (Subobject.ofLE (F₂.F (s + 1) t) (F₂.F s t) (F₂.mono s t)) =
    cokernel.π (Subobject.ofLE (F₁.F (s + 1) t) (F₁.F s t) (F₁.mono s t)) ≫
    cokernel.desc (Subobject.ofLE (F₁.F (s + 1) t) (F₁.F s t) (F₁.mono s t))
      ((cm.filtration_compat s t).choose ≫
        cokernel.π (Subobject.ofLE (F₂.F (s + 1) t) (F₂.F s t) (F₂.mono s t))) _
  rw [cokernel.π_desc]
  -- Both sides are now `_.choose ≫ cokernel.π _`; show the two .choose's agree.
  congr 1
  apply (cancel_mono (F₂.F s t).arrow).mp
  rw [(cm.filtration_compat s t).choose_spec]
  -- Remains: (FC.d_preserves_fil s 1).choose ≫ (F₂.F s t).arrow = (F₁.F s t).arrow ≫ cm.aMap t
  -- This follows from (FC.d_preserves_fil s 1).choose_spec after unfolding twoTermFil/twoTermDiff.
  convert (FC.d_preserves_fil s 1).choose_spec using 1 <;> try rfl
  change (F₁.F s t).arrow ≫ cm.aMap t =
    (twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s 1).arrow ≫
      twoTermDiff (A₁ t) (A₂ t) (cm.aMap t) 1
  simp [twoTermFil, twoTermDiff, twoTermObj]

/-! ### Three-spectra chain

Given a composable pair of convergence morphisms
`V₁ →[f] V₂ →[g] V₃`, the three-spectra chain packages both the
`f`-ESS and `g`-ESS together with their relationship. -/

/-- A composable pair of convergence morphisms `V₁ → V₂ → V₃`. -/
structure ThreeSpectraChain
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    (conv₁ : Convergence E₁ A₁ F₁)
    (conv₂ : Convergence E₂ A₂ F₂)
    (conv₃ : Convergence E₃ A₃ F₃) where
  /-- The first convergence morphism `V₁ → V₂`. -/
  cm₁₂ : ConvergenceMorphism conv₁ conv₂
  /-- The second convergence morphism `V₂ → V₃`. -/
  cm₂₃ : ConvergenceMorphism conv₂ conv₃
  /-- Bounded filtration on the first abutment. -/
  bnd₁ : F₁.IsBounded
  /-- Bounded filtration on the second abutment. -/
  bnd₂ : F₂.IsBounded
  /-- Bounded filtration on the third abutment. -/
  bnd₃ : F₃.IsBounded

/-- The f-extension spectral sequence from the three-spectra chain. -/
noncomputable def ThreeSpectraChain.boundedEssF
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (chain : ThreeSpectraChain conv₁ conv₂ conv₃) :
    BoundedExtensionSS conv₁ conv₂ chain.cm₁₂ chain.bnd₁ chain.bnd₂ :=
  BoundedExtensionSS.mk' conv₁ conv₂ chain.cm₁₂ chain.bnd₁ chain.bnd₂

/-- The g-extension spectral sequence from the three-spectra chain. -/
noncomputable def ThreeSpectraChain.boundedEssG
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (chain : ThreeSpectraChain conv₁ conv₂ conv₃) :
    BoundedExtensionSS conv₂ conv₃ chain.cm₂₃ chain.bnd₂ chain.bnd₃ :=
  BoundedExtensionSS.mk' conv₂ conv₃ chain.cm₂₃ chain.bnd₂ chain.bnd₃

/-! ### Abstract ESS accessors and detection set

These accessors expose the ESS differential and boundary as objects indexed
by abstract `ω`-bidegrees, anchored to the bounded model. The concrete
computation through `(ext.ess t).pageGraded` is left as a follow-up; for now
the bodies are `sorry` so downstream consumers (e.g. `Commutativity.lean`)
can refer to them at the type level. -/

/-- The subtype of abutment elements detected by an E∞ class `y` at bidegree
    `k`. An element `x : T ⟶ F^s A^{k'}` belongs to the detection set of `y`
    if `Detects conv y x` holds, where `(s, k') = conv.reindex k`. -/
def DetectionSet
    {E : SpectralSequence C ω} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) {T : C} (k : ω)
    (y : T ⟶ (E.ssData k).eInfty) :=
  { x : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2) //
    Detects conv y x }

/-- The ESS differential at page `n` from `ω`-bidegree `k₁` to `k₂`, viewed as
    a target object in `C`. -/
noncomputable def BoundedExtensionSS.essDiff
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (_n : ℤ) (_k₁ _k₂ : ω) : C :=
  sorry

/-- The ESS boundary at page `n`, bidegree `k`, viewed as an object in `C`. -/
noncomputable def BoundedExtensionSS.essBoundary
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (_n : ℤ) (_k : ω) : C :=
  sorry

/-- An **$f$-extension** from index `k₁` to `k₂` on page `n`: the ESS
    differential target is nonzero. -/
abbrev HasFExtension
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (n : ℤ) (k₁ k₂ : ω) : Prop :=
  ¬IsZero (ext.essDiff n k₁ k₂)

/-- **ESS 的 non-crossing 唯一性引理**：
    设 ESS（由过滤复形 `ext.complex` 给出的谱序列）中有一条
    微分关系 `d_r` 从 `(s, k)` 到 `(s+r, k-1)`，
    且该关系**不被任何本质关系 cross**。
    则对任意被它 detect 的类（`T` 投射，`x y` 为其源/目标的
    广义元素）以及任意 lift `xl`：若 `xl` 的复形微分落入更深过滤
    （经 `yl` 与 `F^{s+r} ↪ F^s` 的包含分解），则该微分必是
    原目标 `y` 的 lift——即「所关联的微分就是一开始的微分」。
    证明：直接调用 `FilteredComplex.lift_rel_of_not_crossed`。 -/
theorem BoundedExtensionSS.rel_eq_of_not_crossed
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ (ext.complex t).assocGraded s k}
    {y₁ : T ⟶ (ext.complex t).assocGraded (s + r) (k - 1)}
    (h₁ : DifferentialRelation ((ext.complex t).toSpectralSequence (ext.bounded t))
      r ⟨s, k⟩ x y₁)
    (hnc : ¬ RelationCrossedBy ((ext.complex t).toSpectralSequence (ext.bounded t))
      (fun p => p.1) r ⟨s, k⟩ x y₁ h₁)
    {xl : T ⟶ Subobject.underlying.obj ((ext.complex t).fil s k)}
    (hx : (ext.complex t).IsLift s k xl x)
    (yl : T ⟶ Subobject.underlying.obj ((ext.complex t).fil (s + r) (k - 1)))
    (hd : xl ≫ (ext.complex t).filDiff s k =
      yl ≫ Subobject.ofLE ((ext.complex t).fil (s + r) (k - 1))
        ((ext.complex t).fil s (k - 1))
        ((ext.complex t).fil_anti_of_le (k - 1) (by omega))) :
    (ext.complex t).IsLift (s + r) (k - 1) yl y₁ :=
  FilteredComplex.lift_rel_of_not_crossed (ext.complex t) (ext.bounded t)
    r hr s k h₁ hnc hx yl hd

/-! ### 过滤复形的范畴 -/

/-- 过滤复形的**态射**：分次映射族 `f k : FC₁.A k ⟶ FC₂.A k`，
    与微分交换（链映射条件 `d ≫ f = f ≫ d`），且保过滤
    （对每个 `(s, k)` 存在过滤层之间的提升 `φ`，使 `φ ≫ arrow = arrow ≫ f k`）。
    保过滤提升是 ∃-命题数据，供诱导关联分次映射使用。 -/
structure FilteredComplexMorphism (FC₁ FC₂ : FilteredComplex C) where
  /-- 每个次数 `k` 上底层对象之间的映射 -/
  f : ∀ k, FC₁.A k ⟶ FC₂.A k
  /-- 与微分交换：`f k ≫ d k = d k ≫ f (k-1)` -/
  comm_d : ∀ k, f k ≫ FC₂.d k = FC₁.d k ≫ f (k - 1)
  /-- 保过滤：对每个 `(s, k)`，`f k` 在过滤层 `F^s` 之间的限制存在 -/
  filt_compat : ∀ s k,
    ∃ (φ : Subobject.underlying.obj (FC₁.fil s k) ⟶
           Subobject.underlying.obj (FC₂.fil s k)),
      φ ≫ (FC₂.fil s k).arrow = (FC₁.fil s k).arrow ≫ f k

/-- 过滤复形态射在关联分次 `gr^s A^k` 上诱导的映射：
    由保过滤提升经 `cokernel.map` 构造（同 `Filtration.inducedAssocGradedMap` 的模式）。 -/
noncomputable def FilteredComplexMorphism.assocGradedMap
    {FC₁ FC₂ : FilteredComplex C} (g : FilteredComplexMorphism FC₁ FC₂)
    (s k : ℤ) : FC₁.assocGraded s k ⟶ FC₂.assocGraded s k :=
  cokernel.map
    (Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k))
    (Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k))
    (g.filt_compat (s + 1) k).choose
    (g.filt_compat s k).choose
    (by
      apply (cancel_mono ((FC₂.fil s k).arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(g.filt_compat s k).choose_spec, (g.filt_compat (s + 1) k).choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

/-- 过滤复形态射的外延性：两态射的 `f` 分量相同则相等
    （其余字段都是 Prop，proof irrelevance）。 -/
theorem FilteredComplexMorphism.ext {FC₁ FC₂ : FilteredComplex C}
    {g h : FilteredComplexMorphism FC₁ FC₂} (e : g.f = h.f) : g = h := by
  rcases g with ⟨gf, _, _⟩; rcases h with ⟨hf, _, _⟩
  subst e; rfl

/-- 过滤复形的范畴结构：态射为 `FilteredComplexMorphism`。
    恒等取恒等映射族；复合逐分量复合（保过滤提升取两次提升的复合）。
    范畴公理由 `FilteredComplexMorphism.ext` 归约到 `f` 分量。 -/
noncomputable instance : Category (FilteredComplex C) where
  Hom FC₁ FC₂ := FilteredComplexMorphism FC₁ FC₂
  id FC := ⟨fun _ => 𝟙 _, fun _ => by simp, fun _ _ => ⟨𝟙 _, by simp⟩⟩
  comp g h := ⟨fun k => g.f k ≫ h.f k, fun k => by
      rw [Category.assoc, h.comm_d, ← Category.assoc, g.comm_d, Category.assoc],
    fun s k =>
      ⟨(g.filt_compat s k).choose ≫ (h.filt_compat s k).choose, by
        rw [Category.assoc, (h.filt_compat s k).choose_spec,
          ← Category.assoc, (g.filt_compat s k).choose_spec, Category.assoc]⟩⟩
  id_comp g := FilteredComplexMorphism.ext (funext fun k => Category.id_comp (g.f k))
  comp_id g := FilteredComplexMorphism.ext (funext fun k => Category.comp_id (g.f k))
  assoc g h l :=
    FilteredComplexMorphism.ext (funext fun k => Category.assoc (g.f k) (h.f k) (l.f k))

/-- **有界**过滤复形：过滤复形打包其有界性证明（IsBounded 是 Prop 打包进对象）。 -/
structure BoundedFilteredComplex (C : Type u) [Category.{v} C] [Abelian C] where
  /-- 底层过滤复形 -/
  FC : FilteredComplex C
  /-- 过滤有界 -/
  bnd : FC.IsBounded

/-- 有界过滤复形的范畴结构：作为过滤复形范畴的**全子范畴**
    （态射就是底层过滤复形之间的态射，有界性不参与态射的定义）。
    `comp` 用 lambda 直接定义，避免实例中 `≫` 的记法解析歧义。 -/
noncomputable instance : Category (BoundedFilteredComplex C) where
  Hom X Y := FilteredComplexMorphism X.FC Y.FC
  id X := 𝟙 X.FC
  comp {X Y Z} g h :=
    FilteredComplexMorphism.mk (fun k => g.f k ≫ h.f k)
      (fun k => by
        rw [Category.assoc, h.comm_d, ← Category.assoc, g.comm_d, Category.assoc])
      (fun s k =>
        ⟨(g.filt_compat s k).choose ≫ (h.filt_compat s k).choose, by
          rw [Category.assoc, (h.filt_compat s k).choose_spec,
            ← Category.assoc, (g.filt_compat s k).choose_spec, Category.assoc]⟩)
  id_comp {X Y} g :=
    FilteredComplexMorphism.ext (funext fun k => Category.id_comp (g.f k))
  comp_id {X Y} g :=
    FilteredComplexMorphism.ext (funext fun k => Category.comp_id (g.f k))
  assoc {W X Y Z} g h l :=
    FilteredComplexMorphism.ext (funext fun k => Category.assoc (g.f k) (h.f k) (l.f k))

/-! ### toSS 函子：有界过滤复形 ⥤ 谱序列 -/

/-- 过滤复形态射在有界性下诱导的**谱序列态射**。
    `φ k := assocGradedMap`（关联分次上映射，经由 `filt_compat` 提升由
    `cokernel.map` 构造）；保 Z / 保 B / 与 d 交换的证明后续补全（sorry）。 -/
noncomputable def FilteredComplexMorphism.toSpectralSequenceMorphism
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y) :
    X.FC.toSpectralSequence X.bnd ⟶ Y.FC.toSpectralSequence Y.bnd where
  φ := fun ⟨s, k⟩ =>
    FilteredComplexMorphism.assocGradedMap
      (g : FilteredComplexMorphism X.FC Y.FC) s k
  preserves_Z := by sorry
  preserves_B := by sorry
  comm_d := by sorry

/-- 恒等过滤复形态射诱导恒等谱序列态射（φ 分量为关联分次上的恒等）。 -/
theorem FilteredComplexMorphism.toSpectralSequenceMorphism_id
    (X : BoundedFilteredComplex C) :
    (FilteredComplexMorphism.toSpectralSequenceMorphism (𝟙 X)).φ =
      fun _ => 𝟙 _ := by
  sorry

/-- 复合过滤复形态射诱导复合谱序列态射（φ 分量为关联分次上映射的复合）。 -/
theorem FilteredComplexMorphism.toSpectralSequenceMorphism_comp
    {X Y Z : BoundedFilteredComplex C} (g : X ⟶ Y) (h : Y ⟶ Z) :
    (FilteredComplexMorphism.toSpectralSequenceMorphism (g ≫ h)).φ =
      fun k => (FilteredComplexMorphism.toSpectralSequenceMorphism g).φ k ≫
        (FilteredComplexMorphism.toSpectralSequenceMorphism h).φ k := by
  sorry

/-- **toSS 函子**：有界过滤复形范畴到谱序列范畴，
    对象送至 `toSpectralSequence`，态射送至诱导的谱序列态射。 -/
noncomputable def toSS : BoundedFilteredComplex C ⥤ SpectralSequence C (ℤ × ℤ) where
  obj X := X.FC.toSpectralSequence X.bnd
  map := FilteredComplexMorphism.toSpectralSequenceMorphism
  map_id X := SpectralSequenceMorphism.ext
    (FilteredComplexMorphism.toSpectralSequenceMorphism_id X)
  map_comp g h := SpectralSequenceMorphism.ext
    (FilteredComplexMorphism.toSpectralSequenceMorphism_comp g h)

/-! ### convSS ⥤ 有界过滤复形 函子 -/

/-- 收敛谱序列 `X` 在茎次数 `t` 处的**自身两项有界过滤复形**
    `A(t) ⟶[𝟙] A(t)`（恒等映射的两项复形，过滤为 `X.F`），
    作为有界过滤复形范畴的对象。 -/
noncomputable def selfComplex
    (X : ConvergingSS C ω ω') (hb : X.F.IsBounded) (t : ω') :
    BoundedFilteredComplex C :=
  ⟨underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
      (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t,
    underlyingComplexBounded (F₁ := X.F) (F₂ := X.F) (fun (k' : ω') => 𝟙 (X.A k'))
      (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t hb hb⟩

/-- 收敛谱序列之间的态射诱导的**两复形过滤复形态射**：
    次数 `1` 与次数 `0` 处均取 `cm.aMap t`，其余次数取 `0`；
    微分交换由两项复形微分的定义（其余次数微分为 `0`）逐情况验证；
    保过滤性在次数 `1` 由 `F₁.fcId`、次数 `0` 由 `cm.filtration_compat` 给出。
    这里不能在次数 `1` 取恒等：源和目标分别是 `X.A t` 与 `Y.A t`。 -/
noncomputable def toFCMorphism
    {X Y : ConvergingSS C ω ω'} (cm : X ⟶ Y)
    (hbX : X.F.IsBounded) (hbY : Y.F.IsBounded) (t : ω') :
    selfComplex X hbX t ⟶ selfComplex Y hbY t := by
  let component : ∀ k : ℤ,
      (selfComplex X hbX t).FC.A k ⟶ (selfComplex Y hbY t).FC.A k := fun k =>
    if h₁ : k = 1 then
      eqToHom (by simp [selfComplex, underlyingComplex, twoTermObj, h₁]) ≫
        cm.aMap t ≫
          eqToHom (by simp [selfComplex, underlyingComplex, twoTermObj, h₁])
    else if h₀ : k = 0 then
      eqToHom (by simp [selfComplex, underlyingComplex, twoTermObj, h₀]) ≫
        cm.aMap t ≫
          eqToHom (by simp [selfComplex, underlyingComplex, twoTermObj, h₀])
    else 0
  refine
    { f := component
      comm_d := ?_
      filt_compat := ?_ }
  · intro k
    by_cases h₁ : k = 1
    · subst k
      simp [component, selfComplex, underlyingComplex, twoTermDiff, twoTermObj]
    · simp [component, selfComplex, underlyingComplex, twoTermDiff, h₁]
  · intro s k
    by_cases h₁ : k = 1
    · subst k
      simpa [component, selfComplex, underlyingComplex, twoTermFil, twoTermObj] using
        cm.filtration_compat s t
    · by_cases h₀ : k = 0
      · subst k
        simpa [component, selfComplex, underlyingComplex, twoTermFil, twoTermObj] using
          cm.filtration_compat s t
      · refine ⟨0, ?_⟩
        simp [component, selfComplex, underlyingComplex, twoTermFil, twoTermObj, h₁, h₀]

/-- **convSS ⥤ 有界过滤复形函子**：收敛谱序列 `X` 在每个茎次数 `t` 处
    送至其自身的两项复形 `A(t) ⟶[𝟙] A(t)`；
    态射 `cm : X ⟶ Y` 送至 `toFCMorphism cm t`。
    函子性的证明后续补全（sorry）。 -/
noncomputable def convSSToFC
    (hb : ∀ X : ConvergingSS C ω ω', X.F.IsBounded) (t : ω') :
    ConvergingSS C ω ω' ⥤ BoundedFilteredComplex C where
  obj X := selfComplex X (hb X) t
  map cm := toFCMorphism cm (hb _) (hb _) t
  map_id := by sorry
  map_comp := by sorry

/-! ### ESS 函子：两个函子的复合 -/

/-- **ESS 函子**：`convSSToFC t ⋙ toSS` 的复合，
    即收敛谱序列 `X` 在茎次数 `t` 处送至其自身两项复形 `A(t) ⟶[𝟙] A(t)`
    的谱序列（extension spectral sequence）。 -/
noncomputable def ESSFunctor
    (hb : ∀ X : ConvergingSS C ω ω', X.F.IsBounded) (t : ω') :
    ConvergingSS C ω ω' ⥤ SpectralSequence C (ℤ × ℤ) :=
  convSSToFC (C := C) hb t ⋙ toSS

end KIPBase.SpectralSequence
