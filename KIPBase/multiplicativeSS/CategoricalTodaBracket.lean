import KIPBase.Mathlib

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

/-- A Toda-bracket relation in a preadditive category.

`relation x f g h` is a four-place relation.  The object indices enforce that
`f`, `g`, and `h` are composable and that `x` is parallel to their composite.
-/
class CategoricalTodaBracket
    (C : Type u) [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (jugglingSign : C → C → C → C → ℤ) where
  relation : ∀ {X Y Z W : C},
    (X ⟶ W) → (X ⟶ Y) → (Y ⟶ Z) → (Z ⟶ W) → Prop
  composable : ∀ {X Y Z W : C} {x : X ⟶ W} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : Z ⟶ W},
    relation x f g h → f ≫ g = 0 ∧ g ≫ h = 0
  indeterminacy_left : ∀ {X Y Z W : C} {x : X ⟶ W} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : Z ⟶ W},
    relation x f g h → ∀ y : Y ⟶ W, relation (x + f ≫ y) f g h
  indeterminacy_right : ∀ {X Y Z W : C} {x : X ⟶ W} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : Z ⟶ W},
    relation x f g h → ∀ z : X ⟶ Z, relation (x + z ≫ h) f g h
  indeterminacy_complete : ∀ {X Y Z W : C} {x₁ x₂ : X ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W},
    relation x₁ f g h → relation x₂ f g h →
    ∃ (y : Y ⟶ W) (z : X ⟶ Z), x₁ - x₂ = f ≫ y + z ≫ h
  juggling_sign : ∀ X Y Z W : C,
    jugglingSign X Y Z W = 1 ∨ jugglingSign X Y Z W = -1
  juggling : ∀ {X Y Z W V : C} {x : X ⟶ W} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V},
    relation x f g h → h ≫ d = 0 →
    ∃ y : Y ⟶ V,
      relation y g h d ∧ x ≫ d = jugglingSign X Y Z W • (f ≫ y)
  exists_relation : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W),
    f ≫ g = 0 → g ≫ h = 0 → ∃ x : X ⟶ W, relation x f g h

end KIPBase.SpectralSequence
