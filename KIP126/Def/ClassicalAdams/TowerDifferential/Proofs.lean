import KIP126.Def.ClassicalAdams.TowerDifferential.Data

/-!
# The square-zero property of page differentials
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

@[simp] theorem adamsDifferential_mk (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    adamsDifferential unit X r hr s t
      ((adamsCycleBoundaries unit X r hr s t).mkQ x) =
      adamsDifferentialValue unit X r hr s t x := rfl

/-- Every class in the image of the tower-to-layer map is a cycle. -/
theorem adamsDifferential_JToPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : HomotopyGroup (t - s) (adamsTowerAt unit X s)) :
    adamsDifferential unit X r hr s t (adamsJToPage unit X r hr s t x) = 0 := by
  change adamsDifferentialValue unit X r hr s t (adamsJToCycles unit X r hr s t x) = 0
  apply adamsDifferentialValue_eq_zero_of_K
  exact (les_homotopy_exact_g
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (t - s) _).mpr ⟨x, rfl⟩

theorem adamsDifferential_comp (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsPage unit X r hr s t) :
    adamsDifferential unit X r hr (s + r) (t + r - 1)
      (adamsDifferential unit X r hr s t x) = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change adamsDifferential unit X r hr (s + r) (t + r - 1)
      (adamsJToPage unit X r hr (s + r) (t + r - 1)
        (adamsDifferentialLift unit X r hr s t x)) = 0
    exact adamsDifferential_JToPage unit X r hr (s + r) (t + r - 1) _

theorem adamsPageD_target (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsPageD unit X r hr (s, t) (s + r, t + r - 1) =
      ModuleCat.ofHom (adamsDifferential unit X r hr s t) := by
  have h : (classicalAdamsShape r).Rel (s, t) (s + r, t + r - 1) := by
    change (s, t) + ((r : ℤ), (r : ℤ) - 1) = _
    apply Prod.ext <;> dsimp
    omega
  simp only [adamsPageD, dif_pos h, id_eq]
  change ModuleCat.ofHom (adamsDifferential unit X r hr s t) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Consecutive page differentials compose to zero. -/
theorem adamsPageD_comp (r : ℕ) (hr : 1 ≤ r) (p q z : ℤ × ℤ) :
    adamsPageD unit X r hr p q ≫ adamsPageD unit X r hr q z = 0 := by
  classical
  by_cases hpq : (classicalAdamsShape r).Rel p q
  · by_cases hqz : (classicalAdamsShape r).Rel q z
    · have hq : q = (p.1 + r, p.2 + r - 1) := by
        change p + ((r : ℤ), (r : ℤ) - 1) = q at hpq
        rw [← hpq]
        apply Prod.ext <;> dsimp
        omega
      have hz : z = (q.1 + r, q.2 + r - 1) := by
        change q + ((r : ℤ), (r : ℤ) - 1) = z at hqz
        rw [← hqz]
        apply Prod.ext <;> dsimp
        omega
      clear hpq hqz
      subst z
      subst q
      rw [adamsPageD_target, adamsPageD_target]
      ext x
      exact adamsDifferential_comp unit X r hr p.1 p.2 x
    · simp [adamsPageD, hqz]
  · simp [adamsPageD, hpq]

end

end KIP126.Classical.Adams
