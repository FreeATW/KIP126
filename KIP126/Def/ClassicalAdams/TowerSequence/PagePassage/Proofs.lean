import KIP126.Def.ClassicalAdams.TowerSequence.PagePassage.Data

/-!
# Bijectivity of the page-passage quotient map
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Exact-couple page passage is bijective. -/
theorem adamsNextPageToHomology_bijective (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    Function.Bijective (adamsNextPageToHomology unit X r hr p) := by
  sorry

end

end KIP126.Classical.Adams
