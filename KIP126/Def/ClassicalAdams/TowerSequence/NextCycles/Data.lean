import KIP126.Def.ClassicalAdams.TowerPageComplex.Data

/-!
# The next-page cycle map
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The image of a next-page cycle in the current quotient page. -/
def adamsNextCycleToPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unit X (r + 1) (by omega) s t →ₗ[ℤ] adamsPage unit X r hr s t :=
  (adamsCycleBoundaries unit X r hr s t).mkQ.comp
    (Submodule.inclusion (adamsCycles_succ_le unit X r hr s t))

end

end KIP126.Classical.Adams
