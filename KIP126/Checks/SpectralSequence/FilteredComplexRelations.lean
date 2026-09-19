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

end

end KIP126.Challenge.Tools.FilteredComplexRelations
