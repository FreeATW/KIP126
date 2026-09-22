import KIP126.Def.ClassicalAdams.TowerDifferential.Data

/-!
# The square-zero property of page differentials
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Consecutive page differentials compose to zero. -/
theorem adamsPageD_comp (r : ℕ) (hr : 1 ≤ r) (p q z : ℤ × ℤ) :
    adamsPageD unit X r hr p q ≫ adamsPageD unit X r hr q z = 0 := by
  sorry

end

end KIP126.Classical.Adams
