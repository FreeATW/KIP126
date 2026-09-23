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

/-- The only potentially nonzero differential is the map `X₁ ⟶ X₂`. -/
noncomputable def twoTermDiff (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    twoTermObj X₁ X₂ k ⟶ twoTermObj X₁ X₂ (k - 1) :=
  if h : k = 1 then
    eqToHom (show twoTermObj X₁ X₂ k = X₁ by simp [twoTermObj, h]) ≫ f ≫
      eqToHom (show X₂ = twoTermObj X₁ X₂ (k - 1) by simp [twoTermObj, h])
  else 0

/-- A two-term decreasing filtration, with the zero support degrees unconstrained. -/
noncomputable def twoTermFil {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) :
    ℤ → (k : ℤ) → Subobject (twoTermObj X₁ X₂ k) := fun s k =>
  if h₁ : k = 1 then h₁ ▸ fil₁ s
  else if h₀ : k = 0 then h₀ ▸ fil₂ s
  else ⊤

end KIP126.Core.SpectralSequence.BoundedExtension
