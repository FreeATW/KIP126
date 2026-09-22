import KIP126.Def.ClassicalAdams.TowerPages
import KIP126.Def.ClassicalAdams.Page.Data
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Differentials on the quotient pages of an Adams tower

The differential is the quotient of `j(lift(k(x)))`.  The remaining proof
obligations are exact-couple well-definedness properties of this explicit
formula, not data defining an unspecified differential.
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Additivity of the exact-couple differential formula in the target quotient. -/
theorem adamsDifferentialValue_add (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x y : adamsCycles unit X r hr s t) :
    adamsDifferentialValue unit X r hr s t (x + y) =
      adamsDifferentialValue unit X r hr s t x +
        adamsDifferentialValue unit X r hr s t y := by
  sorry

/-- The same formula respects integer scalar multiplication. -/
theorem adamsDifferentialValue_smul (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (n : ℤ) (x : adamsCycles unit X r hr s t) :
    adamsDifferentialValue unit X r hr s t (n • x) =
      n • adamsDifferentialValue unit X r hr s t x := by
  sorry

/-- The differential formula, as a linear map on representatives. -/
def adamsDifferentialOnCycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unit X r hr s t →ₗ[ℤ]
      adamsPage unit X r hr (s + r) (t + r - 1) where
  toFun := adamsDifferentialValue unit X r hr s t
  map_add' := adamsDifferentialValue_add unit X r hr s t
  map_smul' := adamsDifferentialValue_smul unit X r hr s t

/-- An `r`-boundary has zero differential in the target `r`-page. -/
theorem adamsBoundaries_le_differential_ker (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycleBoundaries unit X r hr s t ≤
      LinearMap.ker (adamsDifferentialOnCycles unit X r hr s t) := by
  sorry

/-- The actual page-`r` Adams differential, obtained by quotient descent. -/
def adamsDifferential (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsPage unit X r hr s t →ₗ[ℤ]
      adamsPage unit X r hr (s + r) (t + r - 1) :=
  (adamsCycleBoundaries unit X r hr s t).liftQ
    (adamsDifferentialOnCycles unit X r hr s t)
    (adamsBoundaries_le_differential_ker unit X r hr s t)

/-- The page object as an integer module.  For `H = H𝔽₂`, its mod-two
coefficient structure is a further property of the constructed tower. -/
def adamsPageObject (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) : ModuleCat.{v} ℤ :=
  ModuleCat.of ℤ (adamsPage unit X r hr p.1 p.2)

/-- Extend the prescribed differential by zero outside its bidegree. -/
def adamsPageD (r : ℕ) (hr : 1 ≤ r) (p q : ℤ × ℤ) :
    adamsPageObject unit X r hr p ⟶ adamsPageObject unit X r hr q := by
  classical
  by_cases hpq : (classicalAdamsShape r).Rel p q
  · change p + ((r : ℤ), (r : ℤ) - 1) = q at hpq
    refine ModuleCat.ofHom (adamsDifferential unit X r hr p.1 p.2) ≫ eqToHom ?_
    change adamsPageObject unit X r hr (p.1 + r, p.2 + r - 1) = _
    apply congrArg (adamsPageObject unit X r hr)
    rw [← hpq]
    apply Prod.ext
    · rfl
    · dsimp
      omega
  · exact 0

/-- Consecutive page differentials compose to zero. -/
theorem adamsPageD_comp (r : ℕ) (hr : 1 ≤ r) (p q z : ℤ × ℤ) :
    adamsPageD unit X r hr p q ≫ adamsPageD unit X r hr q z = 0 := by
  sorry

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
