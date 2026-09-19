import KIP126.Def.SpectralSequence.FilteredComplex.Data
import KIP126.Def.Algebra.Completion.Data

/-!
# Bounded extension spectral sequences

This module records the bounded two-term filtered-complex data used by an
extension spectral sequence.  The construction follows ESS-compile's
`Truncation.lean` (commit `11b9ad8`) and KIP-infra's `BoundedExtension.lean`
(commit `65de864`), translated to the canonical KIP126 `FilteredComplex` API.
The corresponding Blueprint source is
`blueprint/src/chapters/extension_spectral_sequences.tex`, node
`def:filtered-two-term-complex`; endpoint and convergence witnesses are kept
in the existing endpoint module rather than duplicated here.
-/

namespace KIP126.Core.SpectralSequence.BoundedExtension

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [CategoryTheory.Category.{v} C] [Abelian C]

/-! ### Two-term complex helpers

These small constructions are the reusable part of the historical bounded
extension file.  They are stated independently of the spectral-sequence
adapter, so later ESS constructions can choose the canonical `FilteredComplex`
representation without introducing a second filtered-complex type. -/

/-- The graded object supported in degrees `1` and `0`. -/
noncomputable def twoTermObj (X₁ X₂ : C) : ℤ → C := fun k =>
  if k = 1 then X₁ else if k = 0 then X₂ else ⊥_ C

@[simp] lemma twoTermObj_one (X₁ X₂ : C) : twoTermObj X₁ X₂ 1 = X₁ := by
  simp [twoTermObj]

@[simp] lemma twoTermObj_zero (X₁ X₂ : C) : twoTermObj X₁ X₂ 0 = X₂ := by
  simp [twoTermObj]

lemma twoTermObj_other (X₁ X₂ : C) (k : ℤ) (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    twoTermObj X₁ X₂ k = ⊥_ C := by
  simp [twoTermObj, h₁, h₀]

/-- The only potentially nonzero differential is the map `X₁ ⟶ X₂`. -/
noncomputable def twoTermDiff (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    twoTermObj X₁ X₂ k ⟶ twoTermObj X₁ X₂ (k - 1) :=
  if h : k = 1 then
    eqToHom (show twoTermObj X₁ X₂ k = X₁ by simp [twoTermObj, h]) ≫ f ≫
      eqToHom (show X₂ = twoTermObj X₁ X₂ (k - 1) by simp [twoTermObj, h])
  else 0

@[simp] lemma twoTermDiff_sq (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    twoTermDiff X₁ X₂ f k ≫ twoTermDiff X₁ X₂ f (k - 1) = 0 := by
  simp only [twoTermDiff]
  by_cases h : k = 1
  · subst k
    change _ ≫ (0 : twoTermObj X₁ X₂ 0 ⟶ twoTermObj X₁ X₂ (-1)) = 0
    simp only [comp_zero]
  · simp [h]

/-- A two-term decreasing filtration, with the zero support degrees unconstrained. -/
noncomputable def twoTermFil {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) :
    ℤ → (k : ℤ) → Subobject (twoTermObj X₁ X₂ k) := fun s k =>
  if h₁ : k = 1 then h₁ ▸ fil₁ s
  else if h₀ : k = 0 then h₀ ▸ fil₂ s
  else ⊤

@[simp] lemma twoTermFil_one {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 1 = fil₁ s := by
  simp [twoTermFil]

@[simp] lemma twoTermFil_zero {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 0 = fil₂ s := by
  simp [twoTermFil]

private lemma twoTermDiff_sq_transport (X₁ X₂ : C) (f : X₁ ⟶ X₂)
    (a b c : ℤ) (hab : a - 1 = b) (hbc : b - 1 = c) :
    (twoTermDiff X₁ X₂ f a ≫ eqToHom (congrArg (twoTermObj X₁ X₂) hab)) ≫
        twoTermDiff X₁ X₂ f b ≫ eqToHom (congrArg (twoTermObj X₁ X₂) hbc) = 0 := by
  subst b
  subst c
  simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
    twoTermDiff_sq X₁ X₂ f a

/-- The canonical chain complex carried by a two-term differential. -/
noncomputable def twoTermComplex (X₁ X₂ : C) (f : X₁ ⟶ X₂) : ChainComplex C ℤ :=
  ChainComplex.of
    (twoTermObj X₁ X₂)
    (fun k => twoTermDiff X₁ X₂ f (k + 1) ≫
      eqToHom (congrArg (twoTermObj X₁ X₂) (by omega : (k + 1) - 1 = k)))
    (fun k => by
      exact twoTermDiff_sq_transport X₁ X₂ f (k + 1 + 1) (k + 1) k
        (by omega) (by omega))

/-- Data for a bounded two-term extension at one graded stem.

The filtered complex is the canonical computational object.  The `two_term`
field records that no other chain degree contributes; endpoint and convergence
witnesses are supplied by the existing endpoint/convergence APIs when a
downstream construction needs them. -/
structure TwoTermData where
  complex : FilteredComplex C
  two_term : ∀ k : ℤ, k ≠ 1 → k ≠ 0 → CategoryTheory.Limits.IsZero (complex.complex.X k)

end KIP126.Core.SpectralSequence.BoundedExtension
