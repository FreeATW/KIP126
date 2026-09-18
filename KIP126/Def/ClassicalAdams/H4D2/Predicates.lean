import KIP126.Def.ClassicalAdams.H4D2.Data

namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

variable {stable : StableHomotopyContext}
  {A : ClassicalAdamsSS stable stable.sphere}

def h₄D₂ (P : SphereAdamsPresentation A) : Prop :=
  ∃ statement : AdamsD₂Statement A,
    statement.source = P.h 4 ∧
      statement.target = sphereProduct P (P.h 0)
        (sphereProduct P (P.h 3) (P.h 3))

def H₄D₂Bound {π₂ : TwoCompleteStableHomotopy stable}
    (system : SpectrumBoundClassicalAdamsSS π₂ stable.sphere)
    (P : SphereAdamsPresentation system.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P) : Prop :=
  Nonempty (H₄D₂BoundData system P algebra)

end KIP126.Classical.Adams
