# Sphere.lean Refactoring — Convert axioms to defs/theorems

## Task 1: `S00` = tensor unit

**Current**: `axiom S00 ... : Syn`
**Target**: `def S00 : Syn := 𝟙_ Syn`

This parallels `SphereSpectrum` in `StableHomotopy/Basic.lean` which is already defined as `𝟙_ 𝒮`.

The definition is trivial. The challenge is that `S00` currently takes many explicit type-class parameters. Change to:
```lean
noncomputable def S00 : Syn := 𝟙_ Syn
```
within the `variable` scope that already has `[MonoidalCategory Syn]`.

**Downstream impact**: `Smn` uses `S00 Syn`. After the change, `S00` no longer takes `Syn` explicitly — it's inferred from the variable scope. Update `Smn` accordingly:
```lean
noncomputable def Smn (m n : ℤ) : Syn :=
  (SyntheticCategory.biShift (m, n)).obj S00
```
Check all uses of `S00 Syn` in downstream files (Sphere.lean, Adams.lean, Nu.lean, etc.) and update.

## Task 2: New axiom — biShift-tensor commutativity

Add to `SyntheticCategory` class (in Basic.lean):
```lean
biShift_tensor_comm : ∀ (p : ℤ × ℤ) (X Y : Syn),
  (biShift p).obj (X ⊗ Y) ≅ (biShift p).obj X ⊗ Y
```

This says "bigraded suspension commutes with tensor product" (suspension distributes over smash product).

**Important**: This changes the `SyntheticCategory` class, so ALL downstream files that provide a `SyntheticCategory` instance or use it will need to account for the new field. In our formalization, `SyntheticCategory` is purely axiomatized (no concrete instances), so this is safe — it just extends the interface.

## Task 3: Prove `biShift_eq_tensor_Smn`

**Goal**:
```lean
theorem biShift_eq_tensor_Smn (m n : ℤ) (X : Syn) :
    (SyntheticCategory.biShift (m, n)).obj X ≅ Smn m n ⊗ X
```

**Proof sketch**:
```
Σ^{m,n} X
  ≅ Σ^{m,n} (𝟙_ ⊗ X)        -- by (MonoidalCategory.leftUnitor X).symm applied via functor
  ≅ (Σ^{m,n} 𝟙_) ⊗ X          -- by biShift_tensor_comm
  = S^{m,n} ⊗ X                -- by definition of Smn
```

In Lean:
1. `(SyntheticCategory.biShift (m,n)).mapIso (MonoidalCategory.leftUnitor X).symm` gives `biShift(m,n).obj X ≅ biShift(m,n).obj (𝟙_ ⊗ X)` (since `leftUnitor.symm : X ≅ 𝟙_ ⊗ X`)

Wait, `leftUnitor X : 𝟙_ ⊗ X ≅ X`, so `leftUnitor.symm : X ≅ 𝟙_ ⊗ X`.

So:
```
biShift(m,n).obj X
  ≅[biShift(m,n).mapIso (λ_ X).symm] biShift(m,n).obj (𝟙_ ⊗ X)
  ≅[biShift_tensor_comm (m,n) 𝟙_ X] biShift(m,n).obj 𝟙_ ⊗ X    -- note: S00 = 𝟙_
  = Smn m n ⊗ X
```

The last step is definitional (if `S00 = 𝟙_` and `Smn m n = biShift(m,n).obj S00`).

In Lean 4:
```lean
theorem biShift_eq_tensor_Smn (m n : ℤ) (X : Syn) :
    (SyntheticCategory.biShift (m, n)).obj X ≅ Smn m n ⊗ X :=
  (SyntheticCategory.biShift (m, n)).mapIso (MonoidalCategory.leftUnitor X).symm ≪≫
    SyntheticCategory.biShift_tensor_comm (m, n) (𝟙_ Syn) X
```

**Note**: `leftUnitor` in Mathlib might be `λ_` notation. Check: `MonoidalCategory.leftUnitor` or `(λ_ X)`. Also the tensor comm axiom gives `biShift(p).obj (X ⊗ Y) ≅ biShift(p).obj X ⊗ Y`, so with `X := 𝟙_`, `Y := X_original`, we get `biShift(p).obj (𝟙_ ⊗ X) ≅ biShift(p).obj 𝟙_ ⊗ X = Smn m n ⊗ X`.

## Task 4: Prove `susp_invariance` (convert axiom → theorem)

**Goal**:
```lean
(Smn m n ⟶ X) ≃ (Smn (m+k) (n+l) ⟶ biShift(k,l).obj X)
```

**Proof sketch**: `biShift(k,l)` is an autoequivalence (it has an inverse `biShift(-k,-l)` via `biShift_comp`). Any equivalence of categories `F : C ≃ C` gives `(A ⟶ B) ≃ (F A ⟶ F B)`.

More concretely:
```
Smn (m+k) (n+l) = biShift(m+k, n+l).obj S00
                 ≅ (biShift(m,n) ⋙ biShift(k,l)).obj S00    -- by biShift_comp inverse
                 = biShift(k,l).obj (biShift(m,n).obj S00)
                 = biShift(k,l).obj (Smn m n)
```

So `(Smn m n ⟶ X)` and `(Smn(m+k)(n+l) ⟶ biShift(k,l).obj X)` are both identified with `(biShift(k,l).obj (Smn m n) ⟶ biShift(k,l).obj X)` up to the iso on `Smn(m+k)(n+l) ≅ biShift(k,l).obj (Smn m n)`.

The equivalence on Hom-sets comes from `biShift(k,l)` being a functor:
```
biShift(k,l).map : (Smn m n ⟶ X) → (biShift(k,l).obj (Smn m n) ⟶ biShift(k,l).obj X)
```
Then precompose with the iso on the source to get to `(Smn(m+k)(n+l) ⟶ biShift(k,l).obj X)`.

For the equivalence (≃ not just →), use that `biShift(k,l)` is faithful+full (since `biShift(-k,-l)` is an inverse up to iso). Concretely, construct the inverse by applying `biShift(-k,-l)` and using `biShift_comp` isos.

**Lean approach**: This may be complex. The prover should:
1. Construct the iso `Smn(m+k)(n+l) ≅ biShift(k,l).obj (Smn m n)` using `biShift_comp`
2. Use `Equiv.mk` with forward = `biShift(k,l).map ≫ (iso.hom ≫ ·)` and backward via `biShift(-k,-l)` + isos
3. If the biShift iso bookkeeping is too complex, axiomatize `biShift_equiv : (A ⟶ B) ≃ (biShift(p).obj A ⟶ biShift(p).obj B)` as a sub-lemma

## Task 5: Prove `lambdaAction` (convert axiom → theorem)

**Goal**:
```lean
(Smn m n ⟶ X) → (Smn m (n+1) ⟶ X)
```

**Proof sketch**: Given `f : Smn m n ⟶ X`, define `lambdaAction f` as the composite:
```
Smn m (n+1)
  = biShift(m, n+1).obj S00
  ≅[biShift_comp(0,-1)(m,n+1+(-1)=n).inv...] biShift(m,n).obj (biShift(0,-1).obj S00)
```

Hmm, this is getting complicated. Simpler approach:

```
Smn m (n+1) = biShift(m,n+1).obj S00
            ≅ biShift(m,n).obj (biShift(0,1).obj S00)    [via biShift_comp]
```

Wait, we want to precompose with λ. The λ-action goes `π_{m,n}(X) → π_{m,n+1}(X)`, i.e., it shifts the second grading UP by 1.

Since `lam : biShift(0,-1) ⟶ 𝟭`, the naturality gives us for any `A`:
`lam.app A : biShift(0,-1).obj A ⟶ A`

Consider `A = Smn m (n+1) = biShift(m,n+1).obj S00`. Then:
`lam.app (Smn m (n+1)) : biShift(0,-1).obj (Smn m (n+1)) ⟶ Smn m (n+1)`

And `biShift(0,-1).obj (Smn m (n+1)) = biShift(0,-1).obj (biShift(m,n+1).obj S00)`.

Using `biShift_comp (m,n+1) (0,-1) : biShift(m,n+1) ⋙ biShift(0,-1) ≅ biShift(m+0, n+1+(-1)) = biShift(m,n)`.

So `biShift(0,-1).obj (biShift(m,n+1).obj S00) ≅ biShift(m,n).obj S00 = Smn m n`.

Then `lambdaAction f` is: `iso.hom ≫ lam.app(Smn m (n+1)) ≫ f`:
```
Smn m (n+1) →[... iso ...] biShift(0,-1).obj (Smn m (n+1))    NO wait, wrong direction
```

Actually, let me reconsider. We want `Smn m (n+1) ⟶ X`, given `f : Smn m n ⟶ X`.

Strategy: find a map `Smn m (n+1) ⟶ Smn m n`, then compose with `f`.

The map `lam.app` gives `biShift(0,-1).obj A ⟶ A`. With `A = Smn m (n+1)`:

`biShift(0,-1).obj (Smn m (n+1)) ⟶ Smn m (n+1)`, which is `biShift(0,-1).obj (biShift(m,n+1).obj S00) ⟶ Smn m (n+1)`.

But we want the other direction: `Smn m (n+1) ⟶ Smn m n`.

Try with `biShift_comp`: 
`biShift_comp (0,-1) (m,n+1) : biShift(0,-1) ⋙ biShift(m,n+1) ≅ biShift(0+m, -1+(n+1)) = biShift(m,n)`.

So `(biShift(0,-1) ⋙ biShift(m,n+1)).obj S00 ≅ biShift(m,n).obj S00 = Smn m n`.

And `(biShift(0,-1) ⋙ biShift(m,n+1)).obj S00 = biShift(m,n+1).obj (biShift(0,-1).obj S00)`.

Now `lam.app S00 : biShift(0,-1).obj S00 ⟶ S00`.

Apply `biShift(m,n+1).map`:
`biShift(m,n+1).map (lam.app S00) : biShift(m,n+1).obj (biShift(0,-1).obj S00) ⟶ biShift(m,n+1).obj S00 = Smn m (n+1)`.

So we have: `Smn m n ≅ biShift(m,n+1).obj (biShift(0,-1).obj S00) →[biShift(m,n+1).map (lam.app S00)] Smn m (n+1)`.

This gives a map `Smn m n → Smn m (n+1)` (wrong direction for precomposition!).

For `lambdaAction`, we want precomposition: `f ↦ (something ≫ f)` where `something : Smn m (n+1) ⟶ Smn m n`. 

Hmm. The λ-action on homotopy groups goes `π_{m,n} → π_{m,n+1}` because `λ` shifts weight DOWN by 1 (from `biShift(0,-1)` to identity), so composing `f : S^{m,n} → X` with the "λ-shift" on the source means we need to look at `S^{m,n+1} → S^{m,n}` but that's not what λ gives.

**Actually**: The λ-action is POST-composition, not pre-composition. Or rather, the standard convention may differ. Let me re-read the hint:

> Given `f : Smn m n ⟶ X`, define `lambdaAction f` as the composite `Smn m (n+1) →[biShift_comp iso] biShift(0,-1).obj (Smn m n) →[lam.app (Smn m n)] Smn m n →[f] X`

So the map is:
```
Smn m (n+1) →[iso] biShift(0,-1).obj (Smn m n) →[lam.app (Smn m n)] Smn m n →[f] X
```

We need the iso: `Smn m (n+1) ≅ biShift(0,-1).obj (Smn m n)`.

`Smn m (n+1) = biShift(m, n+1).obj S00`
`biShift(0,-1).obj (Smn m n) = biShift(0,-1).obj (biShift(m,n).obj S00)`

And `biShift_comp (m,n) (0,-1) : biShift(m,n) ⋙ biShift(0,-1) ≅ biShift(m+0, n+(-1)) = biShift(m, n-1)`.

Hmm, `n + (-1) = n - 1`, not `n + 1`. Let me try the other order:

`biShift_comp (0,-1) (m,n) : biShift(0,-1) ⋙ biShift(m,n) ≅ biShift(0+m, -1+n) = biShift(m, n-1)`.

Neither gives `(m, n+1)`. 

Let's try: we want `biShift(0,-1).obj (biShift(m,n).obj S00) ≅ biShift(m, n+1).obj S00`?

`(biShift(m,n) ⋙ biShift(0,-1)).obj S00 = biShift(0,-1).obj (biShift(m,n).obj S00)`
`biShift_comp (m,n) (0,-1) : biShift(m,n) ⋙ biShift(0,-1) ≅ biShift(m, n-1)`

So `biShift(0,-1).obj (Smn m n) ≅ Smn m (n-1)`. NOT `Smn m (n+1)`.

**Resolution**: The hint says `Smn m (n+1)` but actually we should use `Smn m (n-1)`, OR the convention is different. Let's check: if `lam : biShift(0,-1) ⟶ Id`, and we precompose `f : Smn m n → X` with `lam.app (Smn m n) : biShift(0,-1).obj (Smn m n) → Smn m n`, we get a map `biShift(0,-1).obj (Smn m n) → X`. And `biShift(0,-1).obj (Smn m n) ≅ Smn m (n-1)`. So the result is in `(Smn m (n-1) ⟶ X)` = `π_{m, n-1}(X)`.

This means `lambdaAction` should go `π_{m,n}(X) → π_{m,n-1}(X)`, i.e., the lambda action DECREASES the second grading.

But the current axiom signature says `(Smn m n ⟶ X) → (Smn m (n + 1) ⟶ X)`. This maps `π_{m,n} → π_{m,n+1}`.

**Possible fix**: The current axiom has the wrong direction, OR the convention is that λ acts by post-composition, OR there's a sign convention. The user hint's proof sketch explicitly says `n+1`, so let's trust the signature. Perhaps the iso goes the other way: use `biShift(0,1)` and the fact that `biShift(0,-1)` is an equivalence.

**Pragmatic approach for the prover**: Define `lambdaAction` as a composition using the available iso infrastructure. If the types don't work out cleanly, adjust the proof sketch. The key is to use `lam.app`, `biShift_comp`, and the functor isos.

**If this proves too hard**: Keep as axiom. The biShift iso bookkeeping for this particular construction is complex enough that axiomatization is acceptable. The prover should try for ~20 minutes then report.
