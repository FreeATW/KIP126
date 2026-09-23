import KIP126.Def.ClassicalAdams.SphereSequence.Data

namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

/-! ### The h₄ regression relation -/

/-- A page-2 differential relation whose map is the actual Mathlib page
differential component. -/
structure AdamsD₂Statement {stable : StableHomotopyContext}
    {X : stable.Spectrum} (A : ClassicalAdamsSS stable X) where
  source : AdamsClass A
  target : AdamsClass A
  target_degree : target.degree = classicalAdamsTarget 2 source.degree
  representative_relation :
    (A.d₂ source.degree).hom source.representative =
      transportRepresentative target
        (degree := classicalAdamsTarget 2 source.degree) target_degree

variable {stable : StableHomotopyContext}
  {A : ClassicalAdamsSS stable stable.sphere}

structure H₄D₂BoundData {π₂ : TwoCompleteStableHomotopy stable}
    (system : SpectrumBoundClassicalAdamsSS π₂ stable.sphere)
    (P : SphereAdamsPresentation system.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P) where
  strongConvergence : StrongClassicalAdamsConvergence π₂ stable.sphere
    system.pageSlice.sequence
  strongConvergence_eq : strongConvergence = system.strongConvergence
  lawfulAlgebra : SphereAdamsAlgebraPresentation P
  lawfulAlgebra_eq : lawfulAlgebra = algebra
  statement : ∃ statement : AdamsD₂Statement system.pageSlice,
      statement.source = P.h 4 ∧
        statement.target = sphereProduct P (P.h 0)
          (sphereProduct P (P.h 3) (P.h 3)) ∧
        statement.source.degree = (1, 16) ∧
        statement.target.degree = (3, 17)

end KIP126.Classical.Adams
