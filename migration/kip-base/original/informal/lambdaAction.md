# lambdaAction — Constructing the λ-action on bigraded homotopy groups

## Goal

Fill the sorry in `lambdaAction` (Synthetic/Sphere.lean line 84–89).

**Current signature:**
```lean
noncomputable def lambdaAction (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (m n : ℤ) (X : Syn) :
    (Smn (Syn := Syn) m n ⟶ X) → (Smn (Syn := Syn) m (n - 1) ⟶ X)
```

## Construction

Given `f : Smn m n ⟶ X`, we need to produce `Smn m (n-1) ⟶ X`.

**Key idea**: `Smn m (n-1) = biShift(m, n-1).obj S00` and `Smn m n = biShift(m,n).obj S00`. We have `lam : biShift(0,-1) ⟶ 𝟭 Syn`. The λ-action is precomposition with a canonical map `Smn m (n-1) ⟶ Smn m n` derived from `lam`.

**Step-by-step construction of the map `Smn m (n-1) ⟶ Smn m n`:**

1. By `biShift_comp`, we have:
   `biShift(m, n-1) ≅ biShift(0,-1) ⋙ biShift(m, n)`
   because `(0,-1) + (m,n) = (m, n-1)`.
   
   Wait, `biShift_comp a b : biShift a ⋙ biShift b ≅ biShift(a+b)`. So:
   `biShift_comp (m,n) (0,-1) : biShift(m,n) ⋙ biShift(0,-1) ≅ biShift((m,n)+(0,-1)) = biShift(m, n-1)`
   
   This means: `biShift(m,n-1).obj S00 ≅ biShift(0,-1).obj (biShift(m,n).obj S00)`
   i.e., `Smn m (n-1) ≅ biShift(0,-1).obj (Smn m n)`

   The iso is: `(biShift_comp (m,n) (0,-1)).hom.app S00 : (biShift(m,n) ⋙ biShift(0,-1)).obj S00 ⟶ biShift(m,n-1).obj S00`
   i.e., `biShift(0,-1).obj (Smn m n) ⟶ Smn m (n-1)`

   And the inverse: `(biShift_comp (m,n) (0,-1)).inv.app S00 : Smn m (n-1) ⟶ biShift(0,-1).obj (Smn m n)`

2. Apply `lam.app (Smn m n) : biShift(0,-1).obj (Smn m n) ⟶ Smn m n`.

3. Compose: `Smn m (n-1) →[biShift_comp.inv.app S00] biShift(0,-1).obj (Smn m n) →[lam.app (Smn m n)] Smn m n`

4. But we need `(m,n) + (0,-1) = (m, n-1)`. In `ℤ × ℤ`, this is `(m + 0, n + (-1)) = (m, n - 1)`. This should hold by `simp` or explicit `Prod.ext` + `omega`.

**The definition:**
```lean
noncomputable def lambdaAction ... :=
  fun f =>
    have heq : (m, n) + (0, -1) = (m, n - 1) := by ext <;> simp
    have step1 : Smn (Syn := Syn) m (n - 1) ⟶ (SyntheticCategory.biShift (0, -1)).obj (Smn m n) :=
      (heq ▸ (SyntheticCategory.biShift_comp (m, n) (0, -1)).inv.app S00)
    have step2 : (SyntheticCategory.biShift (0, -1)).obj (Smn m n) ⟶ Smn m n :=
      SyntheticCategory.lam.app (Smn m n)
    step1 ≫ step2 ≫ f
```

**Alternative (cleaner):** Use `susp_invariance` or `biShift_fullyFaithful` to construct the map, but the explicit construction above is more direct.

**Important notes for the prover:**
- The `heq` cast `(m, n) + (0, -1) = (m, n - 1)` is critical. Use `Prod.ext` + `omega` or `simp`.
- `(biShift_comp a b).inv.app X` has type `biShift(a+b).obj X ⟶ (biShift a ⋙ biShift b).obj X = biShift(b).obj (biShift(a).obj X)`.
- After the cast, the source type becomes `biShift(0,-1).obj (biShift(m,n).obj S00) = biShift(0,-1).obj (Smn m n)`.
- `lam.app (Smn m n) : biShift(0,-1).obj (Smn m n) ⟶ Smn m n`.
- The final composition is `step1 ≫ step2 ≫ f : Smn m (n-1) ⟶ X`.

**Fallback:** If the cast/transport causes type-checking issues, try:
1. Use `eqToHom` instead of `▸`
2. Define a helper `lamAtSmn : Smn m (n-1) ⟶ Smn m n` separately with explicit casts
3. If all else fails, axiomatize `lamAtSmn` and define `lambdaAction f := lamAtSmn ≫ f`
