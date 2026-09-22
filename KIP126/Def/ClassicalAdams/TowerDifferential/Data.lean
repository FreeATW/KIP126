import KIP126.Def.ClassicalAdams.TowerDifferential.Cycles.Proofs
import KIP126.Def.ClassicalAdams.Page.Data
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Quotient-page differential data
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

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

end

end KIP126.Classical.Adams
