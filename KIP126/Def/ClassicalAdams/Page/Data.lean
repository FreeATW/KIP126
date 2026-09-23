import KIP126.Def.SpectralSequence.PageLevel.Data
import KIP126.Def.Algebra.Coefficients.Data
import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-! Classical Adams page grading, differential shape, and Mathlib sequence type. -/
namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

abbrev Bidegree := ℤ × ℤ

/-- The AIM classical Adams differential degree. -/
def classicalAdamsShift (r : ℕ) : Bidegree := (r, (r : ℤ) - 1)

/-- The target bidegree of a page-`r` classical Adams differential. -/
def classicalAdamsTarget (r : ℕ) (b : Bidegree) : Bidegree :=
  b + classicalAdamsShift r

def classicalAdamsPageLevel : PageLevelConvention where
  firstPage := 2
  admissibleFrom := 2
  page := fun r => r
  cycleLevel := fun r => r - 1
  quotientExponent := fun r => r - 1
  page_first := by norm_num
  page_succ := by intro r; norm_num
  cycle_succ := by intro r; omega
  quotient_succ := by intro r; omega
  cycleLevel_eq_quotientExponent := by intro r; rfl

@[simp] theorem classicalAdamsShift_two :
    classicalAdamsShift 2 = (2, 1) := by
  norm_num [classicalAdamsShift]

@[simp] theorem classicalAdamsTarget_two (b : Bidegree) :
    classicalAdamsTarget 2 b = (b.1 + 2, b.2 + 1) := by
  apply Prod.ext <;> simp [classicalAdamsTarget, classicalAdamsShift]

/-- The pagewise complex shape used by the classical Adams sequence. -/
def classicalAdamsShape (r : ℤ) : ComplexShape Bidegree :=
  ComplexShape.up' (r, r - 1)

@[simp] theorem classicalAdamsShape_two_rel (b : Bidegree) :
    (classicalAdamsShape 2).Rel b (classicalAdamsTarget 2 b) := by
  simp [classicalAdamsShape, classicalAdamsTarget, classicalAdamsShift]

/-- A mod-2 classical Adams spectral sequence, with the differential shape
fixed to `(r,r-1)` and displayed from `E₂`. -/
abbrev ClassicalAdamsSpectralSequence :=
  CategoryTheory.SpectralSequence F2ModuleCat classicalAdamsShape 2

/-! ### Stable-homotopy and page interfaces -/

end KIP126.Classical.Adams
