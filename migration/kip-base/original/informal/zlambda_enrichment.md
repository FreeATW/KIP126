# Informal proof sketch: zlambda_enrichment

## Goal

```
theorem zlambda_enrichment (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn]
    [SyntheticCategory Syn] : EnrichedCategory (ModuleCat (Polynomial ℤ)) Syn
```

## What we need

`EnrichedCategory V C` requires:
1. For each pair `(X, Y : C)`, an object `EnrichedCategory.Hom X Y : V` (here `V = ModuleCat (Polynomial ℤ)`)
2. Composition morphisms in `V`
3. Identity morphisms from the unit of `V`
4. Associativity and unitality

## Strategy (from user hints)

### Step (a): ℤ-enrichment from Preadditive

`Preadditive Syn` gives us that `X ⟶ Y` is an `AddCommGroup`. By `AddCommGroup.intModule`, each `X ⟶ Y` is a `Module ℤ`.

### Step (b): Define λ-action on Hom-sets

Given `f : X ⟶ Y`, define `λ · f` as:
```
(biShift (0,-1)).map f ≫ lam.app Y
```
This gives a map `(X ⟶ Y) → (X ⟶ Y)` using:
- `biShift (0,-1) : Syn ⥤ Syn` applied to `f` gives `biShift(0,-1)(X) ⟶ biShift(0,-1)(Y)`
- `lam : biShift(0,-1) ⟶ 𝟭 Syn` (natural transformation), so `lam.app Y : biShift(0,-1)(Y) ⟶ Y`
- But we need the result to be `X ⟶ Y`, not `biShift(0,-1)(X) ⟶ Y`.

**Problem**: `(biShift (0,-1)).map f` has type `biShift(0,-1)(X) ⟶ biShift(0,-1)(Y)`, and composing with `lam.app Y` gives type `biShift(0,-1)(X) ⟶ Y`. This is NOT `X ⟶ Y`.

**Fix**: Use naturality of `lam`. By naturality: `lam.app X ≫ f = (biShift (0,-1)).map f ≫ lam.app Y`. So the λ-action should be defined as precomposition:
```
λ · f := lam.app X ≫ f
```
Wait, `lam.app X : biShift(0,-1)(X) ⟶ X`, so `lam.app X ≫ f : biShift(0,-1)(X) ⟶ Y`. Still wrong type.

**Actually**: The λ-action on `π_{m,n}(X) = Hom(S_{m,n}, X)` is defined as precomposition by `S_{m,n-1} → biShift(0,-1)(S_{m,n}) → S_{m,n}` where the first map uses the biShift_comp iso and the second is lam. This gives `π_{m,n}(X) → π_{m,n-1}(X)`, NOT an endomorphism of a single Hom-set.

For `EnrichedCategory` over `Polynomial ℤ`, we'd need each `Hom(X,Y)` to be a `Polynomial ℤ`-module, meaning λ acts as an endomorphism of `Hom(X,Y)`.

**Alternative approach**: The λ-action on `Hom(X,Y)` is: for `f : X ⟶ Y`, define
```
λ · f := (biShift_tensor_comm).inv.app X ≫ (tensorLeft (SyntheticCategory.lam_source)).map f ≫ ...
```
This uses the monoidal structure and the fact that λ comes from a morphism `𝟙 → Σ^{0,1}` (or its adjoint).

### Step (c): Extend to Polynomial ℤ module

Once we have an additive λ-action on each `Hom(X,Y)`:
- Use `Polynomial.aeval` or `Polynomial.lift` to extend the ℤ-linear + λ-action to a `Module (Polynomial ℤ)` structure
- Construct `EnrichedCategory` from this module structure

## Difficulty assessment

**Very high**. The main issues are:
1. Defining the correct λ-action as an endomorphism of each `Hom(X,Y)` (not just shifting bigrading)
2. Mathlib's `EnrichedCategory` API may not easily construct instances from existing categorical structure
3. The monoidal coherence required to show λ-action is well-defined and associative

## Lean 4 / Mathlib availability

- `EnrichedCategory` exists in Mathlib (`Mathlib.CategoryTheory.Enriched.Basic`)
- `ModuleCat (Polynomial ℤ)` exists  
- The construction of an enriched category from a preadditive category + extra endomorphism is NOT a standard Mathlib construction
- This likely requires manually constructing all the enriched category data

## Recommendation for prover

Try the following steps in order:
1. Check if `EnrichedCategory.ofPreadditive` or similar exists in Mathlib
2. If not, try to construct `EnrichedCategory` manually by providing:
   - `Hom X Y := ModuleCat.of (Polynomial ℤ) (sorry : Module (Polynomial ℤ) (X ⟶ Y))`
   - Define the `Module (Polynomial ℤ)` instance on `X ⟶ Y` by:
     - Start with `AddCommGroup.intModule` for ℤ-action
     - Define λ-action as an additive endomorphism
     - Use `Polynomial.aeval` to get `Polynomial ℤ`-algebra action
3. If this approach is too complex, leave as sorry with a clear explanation
