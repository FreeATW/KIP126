import KIP126.Def.ClassicalAdams.TowerPages.Proofs

/-!
# The differential formula on cycle representatives
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The differential formula `j(lift(k(x)))`, evaluated in the target
quotient.  Descending this function to a linear map on `adamsPage` requires
the independence-of-lift and boundary calculations. -/
noncomputable def adamsDifferentialValue (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    adamsPage unit X r hr (s + r) (t + r - 1) :=
  (adamsCycleBoundaries unit X r hr (s + r) (t + r - 1)).mkQ
    ⟨adamsJ unit X (s + r) (t + r - 1) (adamsDifferentialLift unit X r hr s t x),
      adamsJ_mem_cycles unit X r hr (s + r) (t + r - 1) _⟩

end

end KIP126.Classical.Adams
