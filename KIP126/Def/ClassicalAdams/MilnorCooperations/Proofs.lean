import KIP126.Def.ClassicalAdams.MilnorCooperations.Data

/-!
# Transport of Milnor cocycles to the first Adams page
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

namespace Sphere

variable (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- A specified Milnor cocycle is a cycle in the actual first Adams page. -/
theorem milnorCocycle_d_zero (s t : ℕ) (x : KIP126.Steenrod.Milnor.cochains s t)
    (hx : KIP126.Steenrod.Milnor.differential s t x = 0) :
    sphereFirstDifferential H s t ((M.coordinates s t).symm x) = 0 := by
  apply (M.coordinates (s + 1) t).injective
  rw [M.differential_coordinates, LinearEquiv.apply_symm_apply, hx, map_zero]

end Sphere

end

end KIP126.Classical.Adams
