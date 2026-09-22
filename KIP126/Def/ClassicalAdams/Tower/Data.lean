import KIP126.Def.StableHomotopy.Context.Data

/-!
# The Adams tower of a spectrum

The input is a unit map `𝟙_ C ⟶ H` in the abstract stable category.  For the
mod-two Adams tower, `H` is the Eilenberg–Mac Lane spectrum `H𝔽₂` with its
unit.  The tower is constructed by iterating fibers of `X ⟶ H ⊗ X`.
No page, differential, named Adams class, or permanence assertion is an input.

This construction makes sense for any `H` and unit map.  Identifying its
spectral sequence with the classical mod-two Adams spectral sequence also
requires the mathematical properties of `H𝔽₂`; this file does not infer them
from the existence of a unit map.
-/

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The fiber, defined as the desuspension of the chosen cofiber. -/
def fiber {X Y : C} (f : X ⟶ Y) : C :=
  (HasFunctorialCofiber.cofib f)⟦(-1 : ℤ)⟧

/-- The inclusion of the fiber into the source. -/
def fiberι {X Y : C} (f : X ⟶ Y) : fiber f ⟶ X :=
  (HasFunctorialCofiber.cofibδ f)⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).hom.app X

/-- The map whose fiber is one step of the Adams tower. -/
def adamsUnit {H : C} (unit : 𝟙_ C ⟶ H) (X : C) : X ⟶ H ⊗ X :=
  (λ_ X).inv ≫ unit ▷ X

/-- The `s`th term of the Adams tower of `X`. -/
def adamsTower {H : C} (unit : 𝟙_ C ⟶ H) (X : C) : ℕ → C
  | 0 => X
  | s + 1 => fiber (adamsUnit unit (adamsTower unit X s))

/-- A successor map of the constructed Adams tower. -/
def adamsTowerStep {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (s : ℕ) :
    adamsTower unit X (s + 1) ⟶ adamsTower unit X s :=
  fiberι (adamsUnit unit (adamsTower unit X s))

/-- The composite of `length` successive tower maps starting at stage `s`. -/
def adamsTowerComposite {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (s : ℕ) :
    (length : ℕ) → (adamsTower unit X (s + length) ⟶ adamsTower unit X s)
  | 0 => 𝟙 _
  | length + 1 =>
    adamsTowerStep unit X (s + length) ≫ adamsTowerComposite unit X s length

/-- The map between two ordered natural-number stages. -/
def adamsTowerMap {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
    (s t : ℕ) (h : s ≤ t) : adamsTower unit X t ⟶ adamsTower unit X s :=
  eqToHom (congrArg (adamsTower unit X) (by omega : t = s + (t - s))) ≫
    adamsTowerComposite unit X s (t - s)

/-- Extend the tower constantly to nonpositive filtrations. -/
def adamsTowerAt {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (s : ℤ) : C :=
  adamsTower unit X s.toNat

/-- The composite between integer-indexed tower terms. -/
def adamsTowerMapAt {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
    (s t : ℤ) (h : s ≤ t) : adamsTowerAt unit X t ⟶ adamsTowerAt unit X s :=
  adamsTowerMap unit X s.toNat t.toNat (by omega)

/-- A layer of the integer-indexed tower, including negative filtrations. -/
def adamsLayerAt {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (s : ℤ) : C :=
  HasFunctorialCofiber.cofib (adamsTowerMapAt unit X s (s + 1) (by omega))

end KIP126.Classical.Adams
