import KIP126.Def.StableHomotopy.Cohomology.Data

/-! Derived representability and functoriality facts for mod-2 theories. -/
namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Shift-adjunction representability of mod-2 cohomology. -/
noncomputable def cohomologyRepresentable_neg
    (H : Mod2EilenbergMacLane (C := C)) (n : ℤ) (X : C) :
    Mod2Cohomology H n X ≃
      (X ⟶ (shiftFunctor C (-n)).obj H.HF2) :=
  (shiftEquiv C n).toAdjunction.homEquiv X H.HF2

@[simp] theorem pullback_id (H : Mod2EilenbergMacLane (C := C))
    (X : C) (n : ℤ) (φ : Mod2Cohomology H n X) :
    Mod2Cohomology.pullback H (𝟙 X) n φ = φ := by
  simp [Mod2Cohomology.pullback]

@[simp] theorem pullback_comp (H : Mod2EilenbergMacLane (C := C))
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ)
    (φ : Mod2Cohomology H n Z) :
    Mod2Cohomology.pullback H (f ≫ g) n φ =
      Mod2Cohomology.pullback H f n
        (Mod2Cohomology.pullback H g n φ) := by
  simp [Mod2Cohomology.pullback, Category.assoc]

end KIP126.StableHomotopy.Cohomology
