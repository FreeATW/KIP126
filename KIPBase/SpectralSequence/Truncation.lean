/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Truncation of filtered objects and convergence morphisms.
Reference: informal/truncation.md
-/

import KIPBase.SpectralSequence.Convergence

universe u v w

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Truncated objects and filtrations

Given a filtration `F` on a graded object `A : ω → C`, the truncation at level
`s₀` produces the quotient `A(k)/F^{s₀+1}(A(k))` with an induced filtration. -/

/-- The truncated object `A(k) / F^{s₀+1}(A(k))`. -/
noncomputable def Filtration.truncatedObj {ω : Type w} {A : ω → C}
    (fil : Filtration A) (s₀ : ℤ) (k : ω) : C :=
  cokernel ((fil.F (s₀ + 1) k).arrow)

/-- The quotient map `A(k) ↠ A(k)/F^{s₀+1}`. -/
noncomputable def Filtration.truncationProj {ω : Type w} {A : ω → C}
    (fil : Filtration A) (s₀ : ℤ) (k : ω) :
    A k ⟶ fil.truncatedObj s₀ k :=
  cokernel.π ((fil.F (s₀ + 1) k).arrow)

/-- The induced filtration on `A/F^{s₀+1}`: level `s` is the image of `F^s`
    in the quotient. -/
noncomputable def Filtration.truncatedFiltration {ω : Type w} {A : ω → C}
    (fil : Filtration A) (s₀ : ℤ) : Filtration (fil.truncatedObj s₀) where
  F s k := imageSubobject ((fil.F s k).arrow ≫ fil.truncationProj s₀ k)
  mono s k := by
    rw [show (fil.F (s + 1) k).arrow ≫ fil.truncationProj s₀ k =
      Subobject.ofLE _ _ (fil.mono s k) ≫ (fil.F s k).arrow ≫ fil.truncationProj s₀ k
      from by rw [← Category.assoc, Subobject.ofLE_arrow]]
    exact imageSubobject_comp_le _ _

/-- The truncated filtration is bounded when the original is bounded below. -/
noncomputable def Filtration.truncatedFiltration_isBounded {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hbb : fil.IsBoundedBelow) (s₀ : ℤ) :
    (fil.truncatedFiltration s₀).IsBounded where
  lo := fun k => min (hbb.lo k) (s₀ + 1)
  hi := fun _ => s₀ + 1
  lo_le_hi := fun _ => min_le_right _ _
  boundedBelow := fun k s hs => by
    have hs' : s ≤ hbb.lo k := le_trans hs (min_le_left _ _)
    have htop : fil.F s k = ⊤ := hbb.boundedBelow k s hs'
    have hiso : IsIso (fil.F s k).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).mpr htop
    change imageSubobject ((fil.F s k).arrow ≫ cokernel.π _) = ⊤
    rw [imageSubobject_iso_comp]
    have h1 : Epi (image.ι (cokernel.π ((fil.F (s₀ + 1) k).arrow))) :=
      epi_of_epi_fac (image.fac _)
    have h2 : IsIso (image.ι (cokernel.π ((fil.F (s₀ + 1) k).arrow))) :=
      isIso_of_mono_of_epi _
    rw [← Subobject.isIso_arrow_iff_eq_top]
    have harr : (imageSubobject (cokernel.π ((fil.F (s₀ + 1) k).arrow))).arrow =
        (imageSubobjectIso _).hom ≫ image.ι _ := by simp [imageSubobject_arrow]
    rw [harr]
    infer_instance
  boundedAbove := fun k s hs => by
    change imageSubobject ((fil.F s k).arrow ≫ cokernel.π _) = ⊥
    have hmono : fil.F s k ≤ fil.F (s₀ + 1) k := by
      suffices ∀ n : ℕ, fil.F (s₀ + 1 + ↑n) k ≤ fil.F (s₀ + 1) k by
        have key := this (s - (s₀ + 1)).toNat
        rwa [show s₀ + 1 + ↑(s - (s₀ + 1)).toNat = s from by omega] at key
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        calc fil.F (s₀ + 1 + ↑(n + 1)) k
            = fil.F (s₀ + 1 + ↑n + 1) k := by push_cast; ring_nf
          _ ≤ fil.F (s₀ + 1 + ↑n) k := fil.mono _ _
          _ ≤ fil.F (s₀ + 1) k := ih
    have hzero : (fil.F s k).arrow ≫ cokernel.π ((fil.F (s₀ + 1) k).arrow) = 0 := by
      rw [show (fil.F s k).arrow = Subobject.ofLE _ _ hmono ≫ (fil.F (s₀ + 1) k).arrow
        from by rw [Subobject.ofLE_arrow]]
      rw [Category.assoc, cokernel.condition, comp_zero]
    simp only [hzero, imageSubobject_zero]

/-! ### Inverse system structure

The truncations form an inverse system: for `s₀ ≤ s₁`, there is a transition
map `A/F^{s₁+1} → A/F^{s₀+1}` since `F^{s₁+1} ≤ F^{s₀+1}`. -/

omit [Abelian C] in
private theorem Filtration.mono_of_le {ω : Type w} {A : ω → C}
    (fil : Filtration A) {s₁ s₂ : ℤ} (h : s₁ ≤ s₂) (k : ω) :
    fil.F s₂ k ≤ fil.F s₁ k := by
  suffices ∀ n : ℕ, fil.F (s₁ + ↑n) k ≤ fil.F s₁ k by
    have key := this (s₂ - s₁).toNat
    rwa [show s₁ + ↑(s₂ - s₁).toNat = s₂ from by omega] at key
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    calc fil.F (s₁ + ↑(n + 1)) k
        = fil.F (s₁ + ↑n + 1) k := by push_cast; ring_nf
      _ ≤ fil.F (s₁ + ↑n) k := fil.mono _ _
      _ ≤ fil.F s₁ k := ih

/-- Transition map `A/F^{s₁+1} → A/F^{s₀+1}` for `s₀ ≤ s₁`. -/
noncomputable def Filtration.truncationTransition {ω : Type w} {A : ω → C}
    (fil : Filtration A) {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (k : ω) :
    fil.truncatedObj s₁ k ⟶ fil.truncatedObj s₀ k :=
  cokernel.desc ((fil.F (s₁ + 1) k).arrow)
    (cokernel.π ((fil.F (s₀ + 1) k).arrow))
    (by have hmono := fil.mono_of_le (show s₀ + 1 ≤ s₁ + 1 by omega) k
        rw [show (fil.F (s₁ + 1) k).arrow =
          Subobject.ofLE _ _ hmono ≫ (fil.F (s₀ + 1) k).arrow
          from by rw [Subobject.ofLE_arrow],
          Category.assoc, cokernel.condition, comp_zero])

/-- Transition maps compose. -/
theorem Filtration.truncationTransition_comp {ω : Type w} {A : ω → C}
    (fil : Filtration A) {s₀ s₁ s₂ : ℤ} (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ ≤ s₂) (k : ω) :
    fil.truncationTransition h₁₂ k ≫ fil.truncationTransition h₀₁ k =
    fil.truncationTransition (le_trans h₀₁ h₁₂) k := by
  apply (cancel_epi (cokernel.π ((fil.F (s₂ + 1) k).arrow))).mp
  change cokernel.π _ ≫ fil.truncationTransition h₁₂ k ≫ fil.truncationTransition h₀₁ k =
    cokernel.π _ ≫ fil.truncationTransition (le_trans h₀₁ h₁₂) k
  simp only [Filtration.truncationTransition]
  rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, cokernel.π_desc]

/-- Projection is compatible with transition: `proj s₁ ≫ transition = proj s₀`. -/
theorem Filtration.truncationProj_transition {ω : Type w} {A : ω → C}
    (fil : Filtration A) {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (k : ω) :
    fil.truncationProj s₁ k ≫ fil.truncationTransition h k =
    fil.truncationProj s₀ k :=
  cokernel.π_desc _ _ _

/-! ### Truncated convergence morphisms

A convergence morphism induces maps between truncated objects and preserves
the truncated filtrations. -/

/-- The induced map on truncated objects from a convergence morphism. -/
noncomputable def ConvergenceMorphism.truncatedAMap
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (k' : ω') :
    F₁.truncatedObj s₀ k' ⟶ F₂.truncatedObj s₀ k' :=
  cokernel.desc ((F₁.F (s₀ + 1) k').arrow)
    (cm.aMap k' ≫ cokernel.π ((F₂.F (s₀ + 1) k').arrow))
    (by obtain ⟨φ, hφ⟩ := cm.filtration_compat (s₀ + 1) k'
        rw [← Category.assoc, ← hφ, Category.assoc, cokernel.condition, comp_zero])

/-- The truncated aMap preserves truncated filtrations. -/
theorem ConvergenceMorphism.truncatedFiltrationCompat
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (s : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj ((F₁.truncatedFiltration s₀).F s k') ⟶
           Subobject.underlying.obj ((F₂.truncatedFiltration s₀).F s k')),
      φ ≫ ((F₂.truncatedFiltration s₀).F s k').arrow =
        ((F₁.truncatedFiltration s₀).F s k').arrow ≫ cm.truncatedAMap s₀ k' := by
  obtain ⟨φ_s, hφ_s⟩ := cm.filtration_compat s k'
  have sq_comm : φ_s ≫ ((F₂.F s k').arrow ≫ F₂.truncationProj s₀ k') =
      ((F₁.F s k').arrow ≫ F₁.truncationProj s₀ k') ≫ cm.truncatedAMap s₀ k' := by
    rw [Category.assoc, show F₁.truncationProj s₀ k' ≫ cm.truncatedAMap s₀ k' =
      cm.aMap k' ≫ F₂.truncationProj s₀ k' from by
        simp only [Filtration.truncationProj, ConvergenceMorphism.truncatedAMap, cokernel.π_desc]]
    rw [← Category.assoc (F₁.F s k').arrow, ← hφ_s, Category.assoc]
  let sq : Arrow.mk ((F₁.F s k').arrow ≫ F₁.truncationProj s₀ k') ⟶
           Arrow.mk ((F₂.F s k').arrow ≫ F₂.truncationProj s₀ k') :=
    Arrow.homMk φ_s (cm.truncatedAMap s₀ k') sq_comm
  exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩

/-! ### Completeness

A filtration is complete if `A` is the inverse limit of its truncations:
the cone given by the truncation projections satisfies the universal property. -/

/-- A filtration is complete if `A` is the inverse limit of its truncations.
    That is, for each test object `T` and compatible family of maps to the
    truncations, there is a unique lift through `A`. -/
def Filtration.IsComplete {ω : Type w} {A : ω → C}
    (fil : Filtration A) : Prop :=
  ∀ (k : ω) (T : C) (f : ∀ s₀ : ℤ, T ⟶ fil.truncatedObj s₀ k),
    (∀ {s₀ s₁ : ℤ} (h : s₀ ≤ s₁),
      f s₁ ≫ fil.truncationTransition h k = f s₀) →
    ∃! (g : T ⟶ A k), ∀ s₀ : ℤ, g ≫ fil.truncationProj s₀ k = f s₀

end KIPBase.SpectralSequence
