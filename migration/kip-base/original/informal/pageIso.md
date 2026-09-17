# Informal Proof: pageIso — Homology of (E_r, d_r) ≅ E_{r+1}

## Statement

For a spectral sequence with nested subspace data `SSData`, the homology of
`(E_r, d_r)` at bidegree `k` is isomorphic to `E_{r+1}^k`.

## Setup (SSData)

At each bidegree `k`, we have:
- Ambient object `V_k`
- Decreasing chain of subobjects: `Z_0 ⊇ Z_1 ⊇ Z_2 ⊇ ... ⊇ Z_∞`
- Increasing chain of subobjects: `B_0 ⊆ B_1 ⊆ B_2 ⊆ ... ⊆ B_∞`
- `B_r ≤ Z_r` for all `r`
- Page: `E_r = Z_r / B_r` (as a cokernel of the inclusion `B_r ↪ Z_r`)

## The differential

The differential `d_r : E_r^k → E_r^{k + deg_r}` satisfies `d_r ∘ d_r = 0`.

By the nesting structure:
- `ker(d_r)` at bidegree `k` corresponds to `Z_{r+1} / B_r` inside `E_r = Z_r / B_r`
- `im(d_r)` into bidegree `k` corresponds to `B_{r+1} / B_r` inside `ker(d_r) = Z_{r+1} / B_r`

## The isomorphism (Third Isomorphism Theorem)

We need: `H(E_r, d_r) = ker(d_r) / im(d_r) ≅ E_{r+1}`

That is: `(Z_{r+1}/B_r) / (B_{r+1}/B_r) ≅ Z_{r+1}/B_{r+1}`

This is exactly the **Third Isomorphism Theorem**: for a chain of subgroups
`B_r ≤ B_{r+1} ≤ Z_{r+1}`, we have `(Z_{r+1}/B_r) / (B_{r+1}/B_r) ≅ Z_{r+1}/B_{r+1}`.

## Proof for AddCommGroup (concrete)

For `G` an abelian group with subgroups `A ≤ B ≤ G`:
1. `G/A` is the quotient `QuotientAddGroup G A`
2. `B/A` embeds into `G/A` as the image of `B` under the projection `G → G/A`
3. `(G/A) / (B/A)` is `QuotientAddGroup (G/A) (B/A)`
4. The map `G/A → G/B` sending `[g]_A ↦ [g]_B` is well-defined (since `A ≤ B`)
5. Its kernel is exactly `B/A` (since `[g]_B = 0 ↔ g ∈ B ↔ [g]_A ∈ B/A`)
6. By the first isomorphism theorem: `(G/A) / ker ≅ im = G/B`
7. So `(G/A) / (B/A) ≅ G/B`

In our case: `G = Z_{r+1}`, `A = B_r`, `B = B_{r+1}`.
Result: `(Z_{r+1}/B_r) / (B_{r+1}/B_r) ≅ Z_{r+1}/B_{r+1} = E_{r+1}`

## Lean 4 approach for AddCommGrpCat

Since we're working in `AddCommGrpCat`, the objects are bundled `AddCommGroup`s.
The key Mathlib ingredients:
- `Subobject V` in an abelian category is a subobject lattice
- `Subobject.underlying.obj (Z r)` gives the carrier type of the r-cycle subgroup
- `cokernel (Subobject.ofLE B Z h)` gives `Z/B`
- For the third isomorphism theorem, we need to show that the canonical map
  `cokernel(B_r ↪ Z_{r+1}) → cokernel(B_{r+1} ↪ Z_{r+1})` has kernel equal to
  `cokernel(B_r ↪ B_{r+1})`

**Alternative simpler approach for AddCommGrpCat**: Work directly with `AddSubgroup` and
`QuotientAddGroup`, bypassing the categorical `Subobject` machinery:
1. Unwrap `SSData` to get concrete `AddSubgroup`s of the underlying abelian group
2. Use `QuotientAddGroup.quotientQuotientEquivQuotient` (if available) or build it manually
3. Wrap back into `AddCommGrpCat` using `AddCommGrpCat.of`

**Key Mathlib lemma** (VERIFIED to exist):
```
QuotientAddGroup.quotientQuotientEquivQuotient :
  (N : AddSubgroup G) → [nN : N.Normal] →
    (M : AddSubgroup G) → [nM : M.Normal] →
      N ≤ M → (G ⧸ N) ⧸ AddSubgroup.map (QuotientAddGroup.mk' N) M ≃+ G ⧸ M
```
Module: `Mathlib.GroupTheory.QuotientGroup.Basic`

In our case: `G = underlying(Z_{r+1})`, `N = B_r` (as a subgroup of Z_{r+1}), `M = B_{r+1}`.
Then: `(Z_{r+1} ⧸ B_r) ⧸ (B_{r+1}/B_r) ≃+ Z_{r+1} ⧸ B_{r+1}`, i.e. `E_r_homology ≃+ E_{r+1}`.

For abelian groups (AddCommGroup), all subgroups are normal, so the normality conditions are automatic.
