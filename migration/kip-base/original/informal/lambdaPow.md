# lambdaPow — Rewrite λⁿ and Cleanup in Synthetic/Basic.lean

## Task 1: Define `lambdaPow` by induction

**Goal**: Replace the recursive `XModLambdaN` with a proper `lambdaPow` morphism, then redefine `XModLambdaN` as the cofiber of `lambdaPow`.

### Definition

```
lambdaPow (n : ℕ) (X : Syn) : (SyntheticCategory.biShift (0, -(n : ℤ))).obj X ⟶ X
```

By induction on `n`:
- **Base case** `n = 0`: We need a morphism `biShift(0,0).obj X ⟶ X`. Use `biShift_zero.hom.app X : biShift(0,0).obj X ⟶ X` (the component of the natural iso `biShift(0,0) ≅ 𝟭 Syn`).
- **Inductive step** `n + 1`: We need `biShift(0, -(n+1)).obj X ⟶ X`. Construct as:
  1. Start from `biShift(0, -(n+1)).obj X`
  2. Use `biShift_comp` to identify this with `biShift(0,-1).obj (biShift(0,-n).obj X)`:
     - `(SyntheticCategory.biShift_comp (0, -1) (0, -(n : ℤ))).inv.app X` gives us an iso from `biShift(0, -(n+1))` to `biShift(0,-1) ⋙ biShift(0,-n)` (after using that `(0,-1) + (0,-n) = (0,-(n+1))`). Actually be careful: `biShift_comp a b : biShift a ⋙ biShift b ≅ biShift (a + b)`, so `biShift_comp (0,-1) (0,-n) : biShift(0,-1) ⋙ biShift(0,-n) ≅ biShift(0, -(n+1))`. We need the inverse direction: `.inv.app X : biShift(0,-(n+1)).obj X ⟶ (biShift(0,-1) ⋙ biShift(0,-n)).obj X = biShift(0,-n).obj (biShift(0,-1).obj X)`. Wait, `(F ⋙ G).obj X = G.obj (F.obj X)`, so `(biShift(0,-1) ⋙ biShift(0,-n)).obj X = biShift(0,-n).obj (biShift(0,-1).obj X)`.

     Hmm, let's re-examine. We actually want the composition:
     ```
     biShift(0,-(n+1)).obj X
       →[biShift_comp inverse] biShift(0,-n).obj (biShift(0,-1).obj X)
       →[biShift(0,-n).map (lam.app X)] biShift(0,-n).obj X
       →[lambdaPow n X] X
     ```

     Actually wait — `lam : biShift(0,-1) ⟶ 𝟭 Syn`, so `lam.app X : biShift(0,-1).obj X ⟶ X`.

     So the composite is:
     ```
     biShift(0,-(n+1)).obj X
       →[biShift_comp(0,-1)(0,-n).inv.app X] (biShift(0,-1) ⋙ biShift(0,-n)).obj X
       = biShift(0,-n).obj (biShift(0,-1).obj X)
       →[biShift(0,-n).map (lam.app X)] biShift(0,-n).obj X
       →[lambdaPow n X] X
     ```

     **Important**: Check the addition. `(0,-1) + (0,-(n:ℤ)) = (0, -1 + -(n:ℤ)) = (0, -(n+1))`. This uses `Int.neg_add` or similar. We may need `show (0 : ℤ × ℤ).1 + ... = ...` or cast lemmas. The prover should use `congr` or `simp [Int.neg_add]` as needed.

### Redefine XModLambdaN

Once `lambdaPow` is defined:
```
noncomputable def XModLambdaN (X : Syn) (n : ℕ) : Syn :=
  syn_functorial_cofiber.cofib (lambdaPow n X)
```

And derive the cofiber triangle:
```
theorem XModLambdaN.triangle_distinguished (X : Syn) (n : ℕ) :
    Triangle.mk (lambdaPow n X)
      (syn_functorial_cofiber.cofibι (lambdaPow n X))
      (syn_functorial_cofiber.cofibδ (lambdaPow n X)) ∈ distTriang Syn :=
  syn_functorial_cofiber.cofib_distinguished (lambdaPow n X)
```

## Task 2: Merge duplicate — delete `xModLambda_cofiberSeq`

`XModLambda.triangle_distinguished` and `xModLambda_cofiberSeq` express the same fact. Delete `xModLambda_cofiberSeq`. Check no downstream file references it (it was a theorem, not an axiom, so `Grep` for `xModLambda_cofiberSeq` first).

## Task 3: Delete `xModLambdaN_cofiberSeq`

This axiom has conclusion `True` — it's a placeholder. Remove it entirely. The new `XModLambdaN` defined as cofiber of `lambdaPow` gives a real cofiber triangle.

Also remove `lambda_power_cofiber` in `Rigidity.lean` which is proved via `xModLambdaN_cofiberSeq`.

**Downstream check**: Grep for `lambda_power_cofiber` — nothing else references it beyond Rigidity.lean (based on the search).

## Task 4: Prove `zlambda_enrichment` (convert axiom → theorem)

This is a 3-step construction:

### Step (a): ℤ-enrichment from Preadditive

`Preadditive Syn` gives us that Hom-sets are `AddCommGroup`. Mathlib's `Preadditive` already provides `Module ℤ` on Hom-sets via `AddCommGroup.intModule`. So every `(X ⟶ Y)` is a `Module ℤ`.

### Step (b): Define λ-action on Hom(X,Y)

Given `f : X ⟶ Y`, define `λ · f : X ⟶ Y` as:
```
SyntheticCategory.lam.app X ≫ f  -- precompose with λ_X
```
Wait, `lam.app X : biShift(0,-1).obj X ⟶ X`, so `lam.app X ≫ f : biShift(0,-1).obj X ⟶ Y`. This is NOT in `(X ⟶ Y)`.

Alternative using naturality: By naturality of `lam`, we have `biShift(0,-1).map f ≫ lam.app Y = lam.app X ≫ f`. Neither side is in `(X ⟶ Y)`.

**The real construction**: The λ-action on `(X ⟶ Y)` should use the **adjunction** or **enrichment** structure. In the synthetic category, the λ-action on hom-sets is defined by using `biShift(0,-1)` as an autoequivalence and the natural transformation `lam`:

For `f : X ⟶ Y`, define:
```
λ · f := (biShift(0,-1).preimage (lam.app X ≫ f))
```
if `biShift(0,-1)` is fully faithful. But we don't assume that.

**Better approach**: The hint says "use `Polynomial.aeval` or `Polynomial.lift`". The idea is:
- We have `Module ℤ (X ⟶ Y)` from Preadditive
- We need to define a ℤ-algebra map `Polynomial ℤ →+* End(X ⟶ Y)` or equivalently a `Module (Polynomial ℤ) (X ⟶ Y)`
- `Polynomial ℤ ≅ ℤ[X]` and its universal property says: to give a `ℤ[λ]`-module structure on an abelian group `M`, it suffices to give a ℤ-module structure plus a ℤ-linear endomorphism `λ : M → M`.

Actually, the enrichment is over `ModuleCat (Polynomial ℤ)`, meaning each hom-set `(X ⟶ Y)` is a `Module (Polynomial ℤ)`. By `Polynomial.module`, this is equivalent to a `Module ℤ` structure plus an endomorphism `λ_* : (X ⟶ Y) → (X ⟶ Y)` that commutes with the ℤ-action.

**The λ-action on Hom(X,Y)**: This must be an endomorphism of the abelian group `(X ⟶ Y)`. The natural way: `lam` gives `lam.app Y : biShift(0,-1).obj Y ⟶ Y`, and `biShift(0,-1)` applied to `f : X ⟶ Y` gives `biShift(0,-1).map f : biShift(0,-1).obj X ⟶ biShift(0,-1).obj Y`. But to get back to `(X ⟶ Y)` we need to use `biShift_zero` and `biShift_comp`.

**WARNING: This is quite complex.** The prover should attempt this but it may require significant Mathlib API work. If the first attempt fails, we'll axiomatize the intermediate λ-endomorphism and only prove the final `Polynomial.aeval` step.

### Step (c): Polynomial.aeval

Given a `Module ℤ` structure on `(X ⟶ Y)` and a ℤ-linear endomorphism `λ_*`, use `Polynomial.aeval λ_*` to get the `Algebra (Polynomial ℤ) (Module.End ℤ (X ⟶ Y))` action, which gives `Module (Polynomial ℤ) (X ⟶ Y)`. Then package into `EnrichedCategory`.

**Realistic assessment**: Steps (a) and (c) use standard Mathlib. Step (b) requires careful biShift bookkeeping. The prover should focus on (b) — if it can construct a ℤ-linear endomorphism of `(X ⟶ Y)` from `lam`, the rest follows. If step (b) proves too hard due to biShift iso bookkeeping, axiomatize the λ-endomorphism and prove (a)+(c).
