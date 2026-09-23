import KIP126.Def.StableHomotopy.Context.Proofs

/-! Regression checks for the category-theoretic stable-homotopy interface. -/
namespace KIP126.Checks.StableHomotopy

open CategoryTheory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

example (n : ℤ) (X : C) :
    HomotopyGroup n X = (Sphere n ⟶ X) := rfl

example (T : HoCofiberSequence (C := C)) : T.f ≫ T.g = 0 :=
  T.fg_zero

example (T : HoCofiberSequence (C := C)) : T.g ≫ T.h = 0 :=
  T.gh_zero

example (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ∀ (y : HomotopyGroup n T.Y),
      (inducedMap T.g n) y = 0 ↔
        ∃ (x : HomotopyGroup n T.X), (inducedMap T.f n) x = y :=
  les_homotopy_exact_f T n

example (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ∀ (z : HomotopyGroup n T.Z),
      (connectingHomomorphism T n) z = 0 ↔
        ∃ (y : HomotopyGroup n T.Y), (inducedMap T.g n) y = z :=
  les_homotopy_exact_g T n

variable [HasFunctorialCofiber (C := C)]

example {X Y : C} (f : X ⟶ Y) :
    (HoCofiberSequence.ofMorphism f).f = f := rfl

example (n : ℤ) (X : C) :
    (homotopyGroupFunctor (C := C) n).map (𝟙 X) = 𝟙 _ := by
  simp

end KIP126.Checks.StableHomotopy
