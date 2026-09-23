import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Data
import KIP126.Def.ClassicalAdams.Tower.Data

/-! # Unit and multiplication identities used by the Adams comparison -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The Adams unit on `H` is split by its multiplication. -/
theorem adamsUnit_mul : adamsUnit H.unit H.HF2 ≫ R.monoid.mul = 𝟙 H.HF2 := by
  letI := R.monoid
  simp only [adamsUnit, Category.assoc, ← R.one_eq, MonObj.one_mul, Iso.inv_hom_id]

/-- Multiplying the final two factors undoes insertion of the unit. -/
theorem cooperationDiagonal_counit_right :
    cooperationDiagonal H ≫ H.HF2 ◁ R.monoid.mul = 𝟙 (H.HF2 ⊗ H.HF2) := by
  change H.HF2 ◁ adamsUnit H.unit H.HF2 ≫ H.HF2 ◁ R.monoid.mul = _
  rw [← MonoidalCategory.whiskerLeft_comp, adamsUnit_mul, MonoidalCategory.whiskerLeft_id]

end KIP126.StableHomotopy.Cohomology
