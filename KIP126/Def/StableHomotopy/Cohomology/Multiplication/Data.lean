import KIP126.Def.StableHomotopy.Cohomology.Data
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Multiplication on the chosen mod-two Eilenberg--Mac Lane object

This is additional structure on the existing object, with the same unit.
It contains no Adams pages or comparison maps. A Künneth comparison and
the identification of the graded cooperations with the Milnor algebra
remain separate requirements.
-/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- An associative, unital algebra-object structure on the specified `H`
in the chosen monoidal homotopy category. -/
structure Mod2RingStructure (H : Mod2EilenbergMacLane (C := C)) where
  monoid : MonObj H.HF2
  one_eq : monoid.one = H.unit

/-- The graded groups of cooperations, defined from `H ∧ H`. -/
abbrev Mod2Cooperations (H : Mod2EilenbergMacLane (C := C)) (n : ℤ) :=
  Mod2Homology H n H.HF2

/-- Insertion of the unit into the middle factor. After a Künneth
identification this induces the cooperation coproduct. -/
def cooperationDiagonal (H : Mod2EilenbergMacLane (C := C)) :
    H.HF2 ⊗ H.HF2 ⟶ H.HF2 ⊗ (H.HF2 ⊗ H.HF2) :=
  H.HF2 ◁ ((λ_ H.HF2).inv ≫ H.unit ▷ H.HF2)

/-- The map on homotopy groups before applying a Künneth identification. -/
def cooperationDiagonalMap (H : Mod2EilenbergMacLane (C := C)) (n : ℤ) :
    Mod2Cooperations H n →+ HomotopyGroup n (H.HF2 ⊗ (H.HF2 ⊗ H.HF2)) :=
  inducedMap (cooperationDiagonal H) n

/-- Multiplication induces the cooperation counit. -/
def cooperationCounit (H : Mod2EilenbergMacLane (C := C))
    (R : Mod2RingStructure H) (n : ℤ) :
    Mod2Cooperations H n →+ HomotopyGroup n H.HF2 :=
  inducedMap R.monoid.mul n

end KIP126.StableHomotopy.Cohomology
