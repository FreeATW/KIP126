import KIP126.Def.SpectralSequence.UnboundedExtension.TruncatedComplex.Data
import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
import KIP126.Def.SpectralSequence.Truncation.Proofs

/-!
# Boundedness of truncated extension complexes
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

/-- A lower-bounded filtration becomes two-sided bounded after quotient
truncation, hence so does its two-term extension complex. -/
noncomputable def truncatedUnderlyingComplex_isBounded
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') :
    (truncatedUnderlyingComplex cm s₀ t).IsBounded :=
  underlyingComplexBounded
    (fun k' => cm.truncatedAMap s₀ k')
    (fun s k' => cm.truncatedFiltrationCompat s₀ s k') t
    (F₁.truncatedFiltration_isBounded hbb₁ s₀)
    (F₂.truncatedFiltration_isBounded hbb₂ s₀)

end KIP126.Core.SpectralSequence
