# ESS Commutativity — Informal Proof Sketch

Source: Corollary 2.10 from Lin-Wang-Xu "On the Last Kervaire Invariant Problem" (arXiv:2412.10879),
referenced as Proposition 2.12 / Corollary cor:ess-naturality in the project blueprint.

## Setup

**Extension Spectral Sequence (ESS).** For a map `f : X → Y` of spectra, the f-ESS has:
- E₀-page: `E∞(X) ⊕ E∞(Y)`
- Differentials: `d_n^f : ^fE_n^{s,t} → ^fE_n^{s+n,t+n}`
- Z-cycles: `^fZ_{n-1}(X) ⊂ E∞(X)` — elements where d₀^f,...,d_{n-1}^f all vanish
- B-boundaries: `^fB_{n-1}(Y) ⊂ E∞(Y)` — sum of images of d₀^f,...,d_{n-1}^f
- Page decomposition: `^fE_n^{s,t} ≅ ^fZ_{n-1}^{s,t}(X) ⊕ (E∞^{s,t}(Y) / ^fB_{n-1}^{s,t}(Y))`

**Commutative square:**
```
    X --f--> Y
    |        |
    p        q
    ↓        ↓
    Z --g--> W
```
with `q ∘ f ≃ g ∘ p`.

**Degeneration:** `^pE₀ = ^pE_r` means `d_i^p = 0` for `0 ≤ i < r`. Similarly for q.

## Main Theorem: `essCommutativity`

**Statement:** Under degeneration `^pE₀ = ^pE_r` and `^qE₀ = ^qE_r`, for all `n ≥ 0`:
if `d_n^f(x) = y`, `d_r^p(x) = z`, and `d_n^g(z) = w`, then `d_r^q(y) = w`.

**Proof by induction on n:**

### Key lemma: Degeneration implies no crossing

Since `^pE₀ = ^pE_r`, all `d_i^p = 0` for `i < r`. Any potential crossing of `d_r^p(x) = z`
would need `d_m^p(x') = z' ≠ 0` with `m < r` (since `a > 0` forces `m = r - a < r`),
but all such differentials are zero. Similarly for d_r^q.

### Base case (n = 0)

Apply Four-Spectra Corollary with `m = r, n = 0, l = 0`:
1. `d₀^f(x) = y` — given
2. `d_r^p(x) = z` — given
3. `d_r^p` has no crossing — by degeneration
4. `d₀^g(z) = w` has no crossing — d₀ differentials never have crossings (degree constraint: crossing needs `a > 0` and `s+a+m ≤ s+0`, impossible)

Conclusion: `d_{r+0-0}^q(y) = d_r^q(y) = w`.

### Inductive step (n > 0)

Assume commutativity holds for all `i < n`.

Given `d_n^f(x) = y`, `d_r^p(x) = z`, `d_n^g(z) = w`, apply Four-Spectra Corollary
with `m = r, n = n, l = n`:
1. `d_n^f(x) = y` — given
2. `d_r^p(x) = z` — given
3. `d_r^p` has no crossing — by degeneration
4. `d_n^g(z) = w` has no crossing — by inductive hypothesis (the commutativity
   for pages < n ensures the induced map is well-defined, preventing crossings)

Conclusion: `d_{r+n-n}^q(y) = d_r^q(y) = w`. QED.

## Corollary: `essCommutativity_preserves_cycles`

If `x ∈ ^fZ_n(X)` and `d_r^p(x) = z`, then `z ∈ ^gZ_n(Z)`.

**Proof:** For `i ≤ n`: `d_i^g(z) = d_i^g(d_r^p(x)) = d_r^q(d_i^f(x))` by commutativity.
Since `x ∈ ^fZ_n(X)`, `d_i^f(x) = 0`, so `d_r^q(0) = 0`. QED.

## Corollary: `essCommutativity_preserves_boundaries`

If `y ∈ ^fB_n(Y)` and `d_r^q(y) = w`, then `w ∈ ^gB_n(W)`.

**Proof:** Since `y ∈ ^fB_n(Y)`, ∃ `x, i ≤ n` with `d_i^f(x) = y`. By commutativity,
`d_i^g(d_r^p(x)) = d_r^q(d_i^f(x)) = d_r^q(y) = w`. So `w ∈ ^gB_n(W)`. QED.

## Specialization: `essCommutativity_from_AF`

If `AF(p) ≥ r` and `AF(q) ≥ r`, then by Adams filtration vanishing (`af_vanishing`),
`d_i^p = 0` for `i < r` and `d_i^q = 0` for `i < r`, giving the degeneration hypotheses.

## Packaging: `essCommutativity_induces_SS_map`

The pair `(d_r^p, d_r^q)` induces `SpectralSequenceMorphism` from f-ESS to g-ESS:
1. Maps on each page: cycles → cycles, quotient-by-boundaries → quotient-by-boundaries
2. Commutes with differentials by the main theorem
3. Compatible with page isomorphisms by inductive construction

## Proof dependency chain

```
essCommutativity
  ← fourSpectra_cor (Cor 2.9)
    ← fourSpectra (Thm 2.8) — uses no_crossing_iff (Prop 2.7)
  ← Degeneration ⇒ no crossing (from af_vanishing)
  ← Induction on n

essCommutativity_preserves_cycles  ← essCommutativity (direct)
essCommutativity_preserves_boundaries  ← essCommutativity (direct)
essCommutativity_from_AF  ← af_vanishing + essCommutativity
essCommutativity_induces_SS_map  ← all of the above
```

## Note on `essPageIso` (in Extension.lean)

The correct ESS page isomorphism: H(^fE_n, d_n^f) ≅ ^fE_{n+1}, which follows from:
- ker(d_n) at (s,t) = ^fZ_n(X) ⊕ (E∞(Y) / ^fB_{n-1}(Y))
- im(d_n) at (s,t) = ^fB_n(Y) / ^fB_{n-1}(Y)
- Quotient by third isomorphism theorem: (E∞(Y)/B_{n-1}) / (B_n/B_{n-1}) = E∞(Y)/B_n
