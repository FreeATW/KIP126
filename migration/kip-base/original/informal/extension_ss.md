# Extension Spectral Sequence — Informal Content for Formalization

Source: https://github.com/wangguozhen-fudan/spectral-sequence-notes/blob/main/extension.tex

## Setup

Given a morphism of converging spectral sequences `f_E : V₁ → V₂` and an induced map on abutments `f_A : A₁ → A₂`:

1. Treat `f_A` as a two-term filtered complex
2. The **extension spectral sequence** (ESS) is the spectral sequence induced by this filtered complex
3. The E₀-page of the ESS is isomorphic to the E∞-page of V

## Definitions to Formalize

### Notation 2.4: Detection Sets
For `x ∈ E∞^s(V₁)` (at filtration degree s):
- `{x}` = the set of all classes in A₁ detected by x
- `[x]` = a chosen representative class from `{x}`

In Lean: use the existing `Detects` predicate from Convergence.lean. Define:
```
def DetectionSet (conv : Convergence E A F) (k : ω) (y : T ⟶ (E.ssData k).eInfty) :=
  { x : T ⟶ Subobject.underlying.obj (...) // Detects conv y x }
```

### Extension SS Structure
An extension spectral sequence for `f : V₁ → V₂` consists of:
- The underlying SSData at each bidegree (from the two-term filtered complex)
- Differentials `d_n^f : E∞^s(V₁) → E∞^{s+n}(V₂)` (the ESS differentials)
- Boundary groups `ᶠB_{n-1}^{s+n}(V₂)` (the ESS boundary subgroup at page n)

## Propositions

### Proposition 2.5: Characterization of ESS differentials

Given `f : V₁ → V₂`, `x ∈ E∞^s(V₁)`, `y ∈ E∞^{s+n}(V₂)`, `y' ∈ E∞^{s+m}(V₂)` for m,n ≥ 0:

**(1)** `d_n^f(x) = y` ⟺ ∃ `[x] ∈ {x}` such that `f[x] ∈ {y}`.

**(2)** The extension `d_n^f(x) = y` is inessential (y is trivial on E_n page of f-ESS) ⟺
∃ `x' ∈ E∞^{s+a}(V₁)` with `0 < a ≤ n` and essential differential `d_{n-a}^f(x') = y`.
Equivalently: ∃ `[x'] ∈ {x'}` with `Fil(x') > Fil(x)` and `f[x'] ∈ {y}`.

**(3)** If x extends to both y and y':
- (a) If m = n: `y - y' ∈ ᶠB_{n-1}^{s+n}(V₂)` and ∃ `x' ∈ E∞^{s+a}(V₁)` with `0 < a ≤ n` and essential `d_{n-a}^f(x') = y - y'`.
- (b) If m > n: the extension from x to y is inessential.

*Proof sketch*: (1) follows from ESS setup. (2) and (3) follow from (1).

### Remark 2.8: Crossing equivalence

The following are equivalent:
- `d_n^f(x) = y` has no crossing hitting range Fil ≥ p
- For any a > 0, if there is an f-extension from `x' ∈ E∞^{s+a}(V₁)` to nontrivial y', then `Fil(y') < p` or `Fil(y') > Fil(y)`

### Proposition 2.10: No-crossing characterization

`d_n^f(x) = y` has no crossing in Fil ≥ p ⟺ for all `[x] ∈ {x}` with `Fil(f[x]) ≥ p`, we have `f[x] ∈ {y}`.

**Corollary 1**: No crossing at all ⟺ for all `[x] ∈ {x}`, `f[x] ∈ {y}`.
**Corollary 2**: If `d_n^f(x) = 0`, no crossing ⟺ for all `[x] ∈ {x}`, `Fil(f[x]) > Fil(x) + n`.

*Proof sketch (only-if direction)*: By contradiction. If ∃ `[x] ∈ {x}` with `f[x] = [y'] ∉ {y}` and `Fil(y') ≥ p`, then Prop 2.5(3) produces a shorter differential that is a crossing.

*Proof sketch (if direction)*: If a crossing x' → y' exists with `p ≤ Fil(y') ≤ Fil(y)`, then `[x] + [x'] ∈ {x}` but `f([x] + [x']) ∉ {y}` — contradiction.

### Proposition 2.20: Exact sequences and ESS

Given `V₁ →f V₂ →g V₃` with exact sequence `A₁ →π*f A₂ →π*g A₃` at A₂:
All permanent cycles in E∞(V₂) of the g-ESS are boundaries in the f-ESS.

*Proof 1*: The sequence forms a filtered complex. The abutment projected to V₂ is zero, so all permanent g-cycles are killed by f-differentials.

*Proof 2*: If y ∈ E∞(V₂) is a permanent g-cycle, it detects [y] with g([y]) = 0. Exactness gives [x] ∈ A₁ with f([x]) = [y]. If [x] is detected by x, then there is an f-extension from x to y.

## Formalization Strategy

1. Define `ExtensionSS` structure parametrized by a `ConvergenceMorphism` (morphism of converging SS)
2. Axiomatize the ESS differential `d_n^f` as a map between E∞ pages at different filtration degrees
3. Define detection sets using existing `Detects` from Convergence.lean
4. Axiomatize Props 2.5, 2.10, 2.20 — these rely on convergence machinery
5. Use the crossing definitions from Crossing.lean (NoCrossing, NoCrossingRange)
6. The ESS-specific crossing is the crossing of the ESS differentials, which can reuse the general definitions

## Dependencies
- `KIPBase.SpectralSequence.Basic` (SpectralSequence, SSData, Page)
- `KIPBase.SpectralSequence.Convergence` (Filtration, Convergence, Detects, ConvergenceMorphism)
- `KIPBase.SpectralSequence.Crossing` (DifferentialDatum, HasCrossingAt, NoCrossingRange, NoCrossing)
