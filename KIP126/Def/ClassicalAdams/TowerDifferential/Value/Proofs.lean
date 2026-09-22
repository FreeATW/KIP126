import KIP126.Def.ClassicalAdams.TowerDifferential.Value.Data

/-!
# Linearity of the differential formula
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Additivity of the exact-couple differential formula in the target quotient. -/
theorem adamsDifferentialValue_add (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x y : adamsCycles unit X r hr s t) :
    adamsDifferentialValue unit X r hr s t (x + y) =
      adamsDifferentialValue unit X r hr s t x +
        adamsDifferentialValue unit X r hr s t y := by
  sorry

/-- The same formula respects integer scalar multiplication. -/
theorem adamsDifferentialValue_smul (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (n : ℤ) (x : adamsCycles unit X r hr s t) :
    adamsDifferentialValue unit X r hr s t (n • x) =
      n • adamsDifferentialValue unit X r hr s t x := by
  sorry

end

end KIP126.Classical.Adams
