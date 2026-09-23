import KIP126.Def.ClassicalAdams.Convergence.Data

namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

/-- A decreasing filtration is separated when its only subobject contained
in every filtration level is zero.  Unlike eventual vanishing, this permits
the genuine infinite Adams filtration in stem zero. -/
def IsAdamsFiltrationSeparated
    {G : CategoryTheory.GradedObject ℤ AddCommGrpCat}
    (F : KIP126.Core.Algebra.Filtration G) : Prop :=
  ∀ n (S : Subobject (G n)), (∀ s, S ≤ F.F s n) → S = ⊥

end KIP126.Classical.Adams
