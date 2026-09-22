import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Data

/-!
# Next-page cycles have zero current differential
-/

namespace KIP126.Classical.Adams

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- One tower step followed by the layer quotient gives the zero class. -/
theorem adamsJToPage_I_zero (r : ℕ) (hr : 1 ≤ r) (s t a : ℤ)
    (ha : a = s + 1) (y : HomotopyGroup (t - s) (adamsTowerAt unit X a)) :
    adamsJToPage unit X r hr s t (adamsI unit X (t - s) s a (by omega) y) = 0 := by
  subst a
  have hj : adamsJ unit X s t (adamsI unit X (t - s) s (s + 1) (by omega) y) = 0 :=
    (les_homotopy_exact_f
      (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
      (t - s) _).mpr ⟨y, rfl⟩
  have hc : adamsJToCycles unit X r hr s t
      (adamsI unit X (t - s) s (s + 1) (by omega) y) = 0 := Subtype.ext hj
  change (adamsCycleBoundaries unit X r hr s t).mkQ _ = 0
  rw [hc, map_zero]

/-- The representative calculation before converting to the complex's indexing. -/
theorem adamsNextCycle_differential_zero (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X (r + 1) (by omega) s t) :
    adamsDifferential unit X r hr s t (adamsNextCycleToPage unit X r hr s t x) = 0 := by
  let y := adamsCycleLift unit X (r + 1) (by omega) s t x
  let z := adamsI unit X (t - s - 1) (s + r) (s + (r + 1 : ℕ)) (by omega) y
  change adamsDifferentialValue unit X r hr s t
    (Submodule.inclusion (adamsCycles_succ_le unit X r hr s t) x) = 0
  rw [adamsDifferentialValue_eq_of_lift unit X r hr s t _ z (by
    dsimp only [z]
    rw [adamsI_comp]
    exact adamsCycleLift_spec unit X (r + 1) (by omega) s t x)]
  unfold z
  rw [← adamsI_cast unit X (by omega)]
  exact adamsJToPage_I_zero unit X r hr (s + r) (t + r - 1)
    (s + (r + 1 : ℕ)) (by omega) _

/-- A lift killed by the preceding tower map is the connecting image of
an `r`-cycle. This is the exact-couple calculation behind next-page boundaries. -/
theorem adamsCycle_of_lift (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (y : HomotopyGroup (t - s - 1) (adamsTowerAt unit X (s + r)))
    (hy : adamsI unit X (t - s - 1) s (s + r) (by omega) y = 0) :
    ∃ x : adamsCycles unit X r hr s t,
      adamsK unit X s t x = adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega) y := by
  let a := adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega) y
  have ha : adamsI unit X (t - s - 1) s (s + 1) (by omega) a = 0 := by
    dsimp only [a]
    rw [adamsI_comp, hy]
  obtain ⟨x, hx⟩ := (lesHomotopyExactH
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (t - s) a).mp ha
  change adamsK unit X s t x = a at hx
  exact ⟨⟨x, ⟨y, hx.symm⟩⟩, hx⟩

/-- The current-page image of a next-page cycle is killed by the differential. -/
theorem adamsNextCycle_d_zero (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (x : adamsCycles unit X (r + 1) (by omega) p.1 p.2) :
    ((adamsPageComplex unit X r hr).sc p).g
      (adamsNextCycleToPage unit X r hr p.1 p.2 x) = 0 := by
  have hn : (classicalAdamsShape r).next p = (p.1 + r, p.2 + r - 1) := by
    apply ComplexShape.next_eq'
    change p + ((r : ℤ), (r : ℤ) - 1) = _
    apply Prod.ext <;> dsimp
    omega
  let a : adamsPageObject unit X r hr p := adamsNextCycleToPage unit X r hr p.1 p.2 x
  change (adamsPageD unit X r hr p ((classicalAdamsShape r).next p)).hom a = 0
  rw [hn, adamsPageD_target]
  exact adamsNextCycle_differential_zero unit X r hr p.1 p.2 x

end

end KIP126.Classical.Adams
