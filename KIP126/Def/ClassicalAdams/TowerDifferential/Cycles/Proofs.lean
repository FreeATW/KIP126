import KIP126.Def.ClassicalAdams.TowerDifferential.Cycles.Data

/-!
# Vanishing on cycle boundaries
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- An `r`-boundary has zero differential in the target `r`-page. -/
theorem adamsBoundaries_le_differential_ker (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycleBoundaries unit X r hr s t ≤
      LinearMap.ker (adamsDifferentialOnCycles unit X r hr s t) := by
  intro x hx
  obtain ⟨y, _, hy⟩ := hx
  change adamsJ unit X s t y = x.val at hy
  change adamsDifferentialValue unit X r hr s t x = 0
  apply adamsDifferentialValue_eq_zero_of_K
  rw [← hy]
  exact (les_homotopy_exact_g
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (t - s) _).mpr ⟨y, rfl⟩

end

end KIP126.Classical.Adams
