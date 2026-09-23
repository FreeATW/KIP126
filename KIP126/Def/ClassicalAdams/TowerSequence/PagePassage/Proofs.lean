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
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (adamsNextCycleToHomology_eq_zero_iff unit X r hr p y).mp hy
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨x, hx⟩ := (adamsCycleBoundaries unit X r hr p.1 p.2).mkQ_surjective z.val
      have hn : (classicalAdamsShape r).next p = (p.1 + r, p.2 + r - 1) := by
        apply ComplexShape.next_eq'
        change p + ((r : ℤ), (r : ℤ) - 1) = _
        apply Prod.ext <;> dsimp
        omega
      have hd := z.property
      change (adamsPageD unit X r hr p ((classicalAdamsShape r).next p)).hom z.val = 0 at hd
      rw [hn, adamsPageD_target, ← hx] at hd
      change adamsDifferentialValue unit X r hr p.1 p.2 x = 0 at hd
      let x' : adamsCycles unit X (r + 1) (Nat.succ_pos r) p.1 p.2 :=
        ⟨x.val, (adamsDifferentialValue_eq_zero_iff unit X r hr p.1 p.2 x).mp hd⟩
      refine ⟨(adamsCycleBoundaries unit X (r + 1) (Nat.succ_pos r) p.1 p.2).mkQ x', ?_⟩
      change (LinearMap.range ((adamsPageComplex unit X r hr).sc p).moduleCatToCycles).mkQ
        (adamsNextCycleToKernel unit X r hr p x') = _
      apply congrArg (LinearMap.range ((adamsPageComplex unit X r hr).sc p).moduleCatToCycles).mkQ
      exact Subtype.ext hx

end

end KIP126.Classical.Adams
