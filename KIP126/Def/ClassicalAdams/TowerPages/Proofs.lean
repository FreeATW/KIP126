import KIP126.Def.ClassicalAdams.TowerPages.Data
import KIP126.Def.ClassicalAdams.Tower.Proofs

/-!
# Cycle membership and lift properties
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

theorem adamsCycleLift_spec (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega)
      (adamsCycleLift unit X r hr s t x) = adamsK unit X s t x :=
  Classical.choose_spec x.property

/-- A tower-to-layer image is an `r`-cycle on every page. -/
theorem adamsJ_mem_cycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (y : HomotopyGroup (t - s) (adamsTowerAt unit X s)) :
    adamsJ unit X s t y ∈ adamsCycles unit X r hr s t := by
  change adamsK unit X s t (adamsJ unit X s t y) ∈ LinearMap.range _
  refine ⟨0, ?_⟩
  rw [map_zero]
  symm
  exact (les_homotopy_exact_g
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (t - s) _).mpr ⟨y, rfl⟩

/-- Boundaries lie in the cycle submodule on every page. -/
theorem adamsBoundaries_le_cycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsBoundaries unit X r hr s t ≤ adamsCycles unit X r hr s t := by
  rintro x ⟨y, _, rfl⟩
  exact adamsJ_mem_cycles unit X r hr s t y

@[simp] theorem adamsI_self (n s : ℤ) :
    adamsI unit X n s s le_rfl = LinearMap.id := by
  ext x
  simp [adamsI, inducedMap]

theorem adamsI_comp (n s t z : ℤ) (hst : s ≤ t) (htz : t ≤ z)
    (x : HomotopyGroup n (adamsTowerAt unit X z)) :
    adamsI unit X n s t hst (adamsI unit X n t z htz x) =
      adamsI unit X n s z (by omega) x := by
  simp [adamsI, inducedMap, Category.assoc, adamsTowerMapAt_comp]

/-- The boundary filtration increases with the page. -/
theorem adamsBoundaries_le_succ (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsBoundaries unit X r hr s t ≤ adamsBoundaries unit X (r + 1) (by omega) s t := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  change adamsI unit X (t - s) (s - r + 1) s (by omega) y = 0 at hy
  change adamsI unit X (t - s) (s - (r + 1 : ℕ) + 1) s (by omega) y = 0
  rw [← adamsI_comp unit X (t - s) (s - (r + 1 : ℕ) + 1) (s - r + 1) s
    (by omega) (by omega), hy, map_zero]

/-- A cycle which lifts one stage farther is in particular an `r`-cycle. -/
theorem adamsCycles_succ_le (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unit X (r + 1) (by omega) s t ≤ adamsCycles unit X r hr s t := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨adamsI unit X (t - s - 1) (s + r) (s + (r + 1 : ℕ)) (by omega) y, ?_⟩
  rw [adamsI_comp]
  exact hy

end

end KIP126.Classical.Adams
