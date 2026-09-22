import KIP126.Def.ClassicalAdams.TowerSequence.NextHomology.Data

/-!
# Next-page boundaries vanish in current homology
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Next-page boundaries become current-page homology boundaries. -/
theorem adamsNextBoundaries_le_ker (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsCycleBoundaries unit X (r + 1) (by omega) p.1 p.2 ≤
      LinearMap.ker (adamsNextCycleToHomology unit X r hr p) := by
  sorry

end

end KIP126.Classical.Adams
