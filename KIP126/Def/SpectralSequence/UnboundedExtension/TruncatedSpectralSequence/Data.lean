import KIP126.Def.SpectralSequence.UnboundedExtension.TruncatedComplex.Proofs
import KIP126.Def.SpectralSequence.FilteredComplex.SSDataConstruction

/-!
# Truncated extension spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
variable {ω' : Type w}
variable {E₁ E₂ : SpectralSequence C ω}
variable {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
variable {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}

/-- The bounded spectral sequence associated to one quotient truncation of an
otherwise only lower-bounded extension problem. -/
noncomputable def truncatedESS
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') : SpectralSequence C (ℤ × ℤ) :=
  (truncatedUnderlyingComplex cm s₀ t).toSpectralSequence
    (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t)

end KIP126.Core.SpectralSequence
