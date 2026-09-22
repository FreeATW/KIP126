import KIP126.Def.ClassicalAdams.TowerPages.Data

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

/-- A cycle which lifts one stage farther is in particular an `r`-cycle. -/
theorem adamsCycles_succ_le (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unit X (r + 1) (by omega) s t ≤ adamsCycles unit X r hr s t := by
  sorry

end

end KIP126.Classical.Adams
