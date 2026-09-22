import KIP126.Def.ClassicalAdams.TowerDifferential.Value.Proofs

/-!
# The differential as a linear map on cycles
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The differential formula, as a linear map on representatives. -/
def adamsDifferentialOnCycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unit X r hr s t →ₗ[ℤ]
      adamsPage unit X r hr (s + r) (t + r - 1) where
  toFun := adamsDifferentialValue unit X r hr s t
  map_add' := adamsDifferentialValue_add unit X r hr s t
  map_smul' := adamsDifferentialValue_smul unit X r hr s t

end

end KIP126.Classical.Adams
