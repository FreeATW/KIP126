# Functorial Cofiber and Tensor Triangulated Category — Informal Content

## HasFunctorialCofiber

In a triangulated category, for any morphism f : X → Y, there exists a distinguished triangle
X → Y → Z → X[1]. The cofiber Z is unique up to non-unique isomorphism. A **functorial cofiber**
gives a CANONICAL choice: a function `cofib` from morphisms to objects, with canonical structure maps.

### Class definition (general, for any pretriangulated category)

```
class HasFunctorialCofiber (C : Type u) [Category.{v} C]
    [HasShift C ℤ] [Pretriangulated C] where
  /-- Canonical cofiber object for a morphism -/
  cofib : {X Y : C} → (X ⟶ Y) → C
  /-- Inclusion into the cofiber -/
  cofibι : {X Y : C} → (f : X ⟶ Y) → Y ⟶ cofib f
  /-- Connecting map from the cofiber -/
  cofibδ : {X Y : C} → (f : X ⟶ Y) → cofib f ⟶ (shiftFunctor C (1 : ℤ)).obj X
  /-- The cofiber triangle is distinguished -/
  cofib_distinguished : ∀ {X Y : C} (f : X ⟶ Y),
    Triangle.mk f (cofibι f) (cofibδ f) ∈ distTriang C
  /-- Functoriality: commutative squares induce maps on cofibers -/
  cofibMap : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂), α ≫ f₂ = f₁ ≫ β →
    cofib f₁ ⟶ cofib f₂
```

**IMPORTANT**: This class must be defined in a file that does NOT import SH/Basic or Syn/Basic,
to avoid circular dependencies. Suggest putting it in the same TensorTriangulatedCategory.lean
file but BEFORE the ClosedSymmetricTensorTriangulated class (which needs SH/Basic for Sphere).

**Architecture suggestion**: Restructure TensorTriangulatedCategory.lean to NOT import SH/Basic
for the general classes. Keep ClosedSymmetricTensorTriangulated in the same file but make it
parameterized by general category parameters instead of StableHomotopyCategory. Alternatively,
create a new base file `KIPBase/FunctorialCofiber.lean` that only imports Mathlib.

## TensorTriangulatedCatWithFunctorialCofiber

Extends HasFunctorialCofiber with tensor-cofiber compatibility:

```
class TensorTriangulatedCatWithFunctorialCofiber (C : Type u)
    [Category.{v} C] [HasShift C ℤ] [MonoidalCategory C]
    [Pretriangulated C] extends HasFunctorialCofiber C where
  /-- Tensor with W commutes with functorial cofiber:
      cofib(f ⊗ id_W) ≅ cofib(f) ⊗ W -/
  tensorCofibIso : ∀ {X Y : C} (f : X ⟶ Y) (W : C),
    cofib (f ▷ W) ≅ cofib f ⊗ W
```

## Usage in StableHomotopy

In SH/TensorTriangulatedCategory.lean (or SH/Basic.lean), declare:
```
axiom sh_functorialCofiber :
  TensorTriangulatedCatWithFunctorialCofiber 𝒮
```

Then replace `HoCofiberSequence` construction via `distinguished_cocone_triangle` with
`HasFunctorialCofiber.cofib`. The `HoCofiberSequence` structure itself can remain, but
cofiber objects should be obtained canonically from `cofib`.

## Usage in Synthetic

In Syn/Basic.lean, declare (WITHOUT closed monoidal / internal hom):
```
axiom syn_functorialCofiber :
  TensorTriangulatedCatWithFunctorialCofiber Syn
```

Then replace `XModLambda` definition:
```
-- OLD:
noncomputable def XModLambda (X : Syn) : Syn :=
  (distinguished_cocone_triangle (SyntheticCategory.lam.app X)).choose

-- NEW:
def XModLambda (X : Syn) : Syn :=
  HasFunctorialCofiber.cofib (SyntheticCategory.lam.app X)
```

This gives CANONICAL cofibers instead of `Classical.choice`-based ones. The inclusion
and projection maps are also canonical from HasFunctorialCofiber.
