import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Data

/-!
# Next-page cycles have zero current differential
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The current-page image of a next-page cycle is killed by the differential. -/
theorem adamsNextCycle_d_zero (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (x : adamsCycles unit X (r + 1) (by omega) p.1 p.2) :
    ((adamsPageComplex unit X r hr).sc p).g
      (adamsNextCycleToPage unit X r hr p.1 p.2 x) = 0 := by
  sorry

end

end KIP126.Classical.Adams
