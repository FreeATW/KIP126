import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Proofs

/-!
# The homology class of a next-page representative
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The specified map from next-page representatives to current-page cycles. -/
def adamsNextCycleToKernel (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsCycles unit X (r + 1) (by omega) p.1 p.2 →ₗ[ℤ]
      LinearMap.ker ((adamsPageComplex unit X r hr).sc p).g.hom :=
  (adamsNextCycleToPage unit X r hr p.1 p.2).codRestrict _
    (adamsNextCycle_d_zero unit X r hr p)

/-- The homology class of a next-page representative. -/
def adamsNextCycleToHomology (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsCycles unit X (r + 1) (by omega) p.1 p.2 →ₗ[ℤ]
      ((adamsPageComplex unit X r hr).sc p).moduleCatLeftHomologyData.H :=
  (LinearMap.range ((adamsPageComplex unit X r hr).sc p).moduleCatToCycles).mkQ.comp
    (adamsNextCycleToKernel unit X r hr p)

end

end KIP126.Classical.Adams
