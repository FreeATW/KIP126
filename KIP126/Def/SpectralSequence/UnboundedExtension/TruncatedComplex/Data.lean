import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
import KIP126.Def.SpectralSequence.Truncation.Proofs

/-!
# Truncated two-term extension complexes
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

/-- The two-term filtered complex of the convergence morphism after quotient
truncating both target filtrations at `s₀`. -/
noncomputable def truncatedUnderlyingComplex
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') :
    FilteredComplex C :=
  underlyingComplex
    (fun k' => cm.truncatedAMap s₀ k')
    (fun s k' => cm.truncatedFiltrationCompat s₀ s k') t

end KIP126.Core.SpectralSequence
