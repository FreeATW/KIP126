import KIP126.Def.StableHomotopy.Cohomology.Proofs

/-! Regression checks for the explicit mod-2 cohomology interface. -/
namespace KIP126.Checks.StableHomotopy

open CategoryTheory
open KIP126.StableHomotopy
open KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

example (H : Mod2Context (C := C)) (n : ℤ) (X : C) :
    Mod2Cohomology H n X = ((shiftFunctor C n).obj X ⟶ H.HF2) := rfl

example (H : Mod2Context (C := C)) {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    Mod2Cohomology.pullback H f n = Mod2Cohomology.pullback H f n := rfl

example (H : Mod2Context (C := C)) {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    (Mod2Homology.pushforward H f n) 0 = 0 := by
  simp [Mod2Homology.pushforward]

example (H : Mod2Context (C := C)) (n : ℤ) (X : C) :
    Nonempty
      (Mod2Cohomology H n X ≃
        (X ⟶ (shiftFunctor C (-n)).obj H.HF2)) :=
  ⟨cohomologyRepresentable_neg H n X⟩

end KIP126.Checks.StableHomotopy
