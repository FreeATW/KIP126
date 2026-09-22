import KIP126.Def.ClassicalAdams.TowerDifferential.Proofs

/-!
# Adams quotient pages as homological complexes
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The constructed page and differential as a Mathlib complex. -/
def adamsPageComplex (r : ℕ) (hr : 1 ≤ r) :
    HomologicalComplex (ModuleCat.{v} ℤ) (classicalAdamsShape r) where
  X p := adamsPageObject unit X r hr p
  d p q := adamsPageD unit X r hr p q
  shape p q hpq := by
    simp only [adamsPageD, dif_neg hpq]
  d_comp_d' p q z _ _ := adamsPageD_comp unit X r hr p q z

end

end KIP126.Classical.Adams
