import KIP126.Def.ClassicalAdams.TowerSequence.NextHomology.Proofs

/-!
# The quotient map for page passage
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The page-passage map, from the next page to the homology of the current page. -/
def adamsNextPageToHomology (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsPage unit X (r + 1) (by omega) p.1 p.2 →ₗ[ℤ]
      ((adamsPageComplex unit X r hr).sc p).moduleCatLeftHomologyData.H :=
  (adamsCycleBoundaries unit X (r + 1) (by omega) p.1 p.2).liftQ
    (adamsNextCycleToHomology unit X r hr p)
    (adamsNextBoundaries_le_ker unit X r hr p)

end

end KIP126.Classical.Adams
