import KIP126.Def.ClassicalAdams.TowerDifferential.Value.Data

/-!
# Linearity of the differential formula
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Two tower elements with the same image define the same quotient-page class. -/
theorem adamsJToPage_eq (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    {a : ℤ} (ha : a = s - r + 1)
    (x y : HomotopyGroup (t - s) (adamsTowerAt unit X s))
    (h : adamsI unit X (t - s) a s (by omega) x =
      adamsI unit X (t - s) a s (by omega) y) :
    adamsJToPage unit X r hr s t x = adamsJToPage unit X r hr s t y := by
  subst a
  apply (Submodule.Quotient.eq _).mpr
  change adamsJ unit X s t x - adamsJ unit X s t y ∈ adamsBoundaries unit X r hr s t
  refine ⟨x - y, ?_, map_sub _ _ _⟩
  change adamsI unit X (t - s) (s - r + 1) s (by omega) (x - y) = 0
  rw [map_sub, h, sub_self]

/-- Reindexing the homotopy degree commutes with every tower map. -/
theorem adamsI_cast {n n' : ℤ} (e : n = n') (s t : ℤ) (h : s ≤ t)
    (x : HomotopyGroup n (adamsTowerAt unit X t)) :
    adamsI unit X n' s t h
      (Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X t)) e) x) =
      Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X s)) e)
        (adamsI unit X n s t h x) := by
  subst n'
  rfl

omit [HasFunctorialCofiber (C := C)] in
@[simp] theorem homotopyGroup_cast_zero {n n' : ℤ} (e : n = n') (A : C) :
    Eq.mp (congrArg (fun n => HomotopyGroup n A) e) 0 = 0 := by
  subst n'
  rfl

/-- Equality of the connecting images suffices for equality of differential values. -/
theorem adamsDifferentialValue_eq_of_lift (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t)
    (y : HomotopyGroup (t - s - 1) (adamsTowerAt unit X (s + r)))
    (hy : adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega) y =
      adamsK unit X s t x) :
    adamsDifferentialValue unit X r hr s t x =
      adamsJToPage unit X r hr (s + r) (t + r - 1)
        (Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + r)))
          (by omega : t - s - 1 = (t + r - 1) - (s + r))) y) := by
  apply adamsJToPage_eq unit X r hr (s + r) (t + r - 1) (a := s + 1) (by omega)
  simp only [adamsDifferentialLift]
  rw [adamsI_cast unit X (by omega), adamsI_cast unit X (by omega), adamsCycleLift_spec, hy]

/-- Representatives with zero connecting image have zero differential. -/
theorem adamsDifferentialValue_eq_zero_of_K (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) (hx : adamsK unit X s t x = 0) :
    adamsDifferentialValue unit X r hr s t x = 0 := by
  rw [adamsDifferentialValue_eq_of_lift unit X r hr s t x 0 (by simpa using hx.symm)]
  rw [homotopyGroup_cast_zero (by omega), map_zero]

/-- Additivity of the exact-couple differential formula in the target quotient. -/
theorem adamsDifferentialValue_add (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x y : adamsCycles unit X r hr s t) :
    adamsDifferentialValue unit X r hr s t (x + y) =
      adamsDifferentialValue unit X r hr s t x +
        adamsDifferentialValue unit X r hr s t y := by
  rw [adamsDifferentialValue_eq_of_lift unit X r hr s t (x + y)
    (adamsCycleLift unit X r hr s t x + adamsCycleLift unit X r hr s t y) (by
      rw [map_add, adamsCycleLift_spec, adamsCycleLift_spec]
      exact (map_add (adamsK unit X s t) x.val y.val).symm)]
  unfold adamsDifferentialValue adamsDifferentialLift
  have e : t - s - 1 = (t + r - 1) - (s + r) := by omega
  have hcast : ∀ (a b : HomotopyGroup (t - s - 1) (adamsTowerAt unit X (s + r))),
      (Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + r))) e) (a + b)) =
        Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + r))) e) a +
        Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + r))) e) b := by
    generalize t - s - 1 = n at e ⊢
    subst n
    intros
    rfl
  rw [hcast, map_add]

/-- The same formula respects integer scalar multiplication. -/
theorem adamsDifferentialValue_smul (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (n : ℤ) (x : adamsCycles unit X r hr s t) :
    adamsDifferentialValue unit X r hr s t (n • x) =
      n • adamsDifferentialValue unit X r hr s t x := by
  let f : adamsCycles unit X r hr s t →+ adamsPage unit X r hr (s + r) (t + r - 1) :=
    { toFun := adamsDifferentialValue unit X r hr s t
      map_zero' := by
        have h := adamsDifferentialValue_add unit X r hr s t 0 0
        simp only [zero_add] at h
        exact add_left_cancel (h.symm.trans (add_zero _).symm)
      map_add' := adamsDifferentialValue_add unit X r hr s t }
  exact f.map_zsmul n x

end

end KIP126.Classical.Adams
