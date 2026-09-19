import KIP126.Challenge.Tools.FilteredComplexRelations.Statement

/-! Regression check for the canonical filtered-complex page view. -/

namespace KIP126.Challenge.Tools.FilteredComplexRelations

noncomputable section

open CategoryTheory
open KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FilteredComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

example (FC : FilteredComplex C) (W : PageHomologyWitness FC) :
  PageView FC :=
  PageView.ofPageHomologyWitness FC W

example (FC : FilteredComplex C) (W : PageHomologyFactorization FC) :
  PageView FC :=
  PageView.ofPageHomologyFactorization FC W

example (FC : FilteredComplex C) (P : PageView FC)
    {r : ℤ} {hr : P.firstPage ≤ r} {s k : ℤ} {T : C}
    {x : P.element r hr s k T}
    {xl₁ xl₂ : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    (h₁ : P.IsLift r hr s k xl₁ x)
    (h₂ : P.IsLift r hr s k xl₂ x) :
    (FC.boundarySubobject s k (P.pageNumber r hr)).Factors
      ((xl₁ - xl₂) ≫ FC.filtration.toAssociatedGraded s k) :=
  P.isLift_sub_factors_boundary h₁ h₂

end

end KIP126.Challenge.Tools.FilteredComplexRelations
