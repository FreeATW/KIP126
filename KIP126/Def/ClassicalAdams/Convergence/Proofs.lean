import KIP126.Def.ClassicalAdams.Convergence.Predicates

namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

theorem isAdamsFiltrationSeparated_of_eventuallyZero
    {G : CategoryTheory.GradedObject ℤ AddCommGrpCat}
    (F : KIP126.Core.Algebra.Filtration G)
    (hF : F.IsEventuallyZero) :
    IsAdamsFiltrationSeparated F := by
  intro n S hS
  obtain ⟨s, hs⟩ := hF n
  apply le_antisymm
  · have h := hS s
    rw [hs] at h
    exact h
  · exact bot_le

end KIP126.Classical.Adams
