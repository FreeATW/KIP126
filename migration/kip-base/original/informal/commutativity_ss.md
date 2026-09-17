# Commutativity of Extension Spectral Sequence Differentials — Informal Content

Source: https://github.com/wangguozhen-fudan/spectral-sequence-notes/blob/main/commutativity.tex

## Setup

A homotopy commutative square of converging spectral sequences:
```
V₁ --f--> V₂
|p        |q
v         v
V₃ --g--> V₄
```

Classes:
- `x ∈ E∞^s(V₁)`, `y ∈ E∞^{s+n}(V₂)`, `z ∈ E∞^{s+m}(V₃)`, `w ∈ E∞^{s+m+l}(V₄)`

Uses Proposition 2.5 and 2.10 from Extension.lean.

## Main Results

### Theorem 2.12: Commutativity Theorem

**Hypotheses**: m, n, l ≥ 0, 0 < k ≤ m + l − n:
1. `d_n^f(x) = y`
2. `d_m^p(x) = z`
3. Differential in (1) or (2) has no crossing
4. `d_l^g(z) = w`, and has no crossing hitting Fil ≥ s + n + k
5. `d_{k-1}^q(y) = 0`, and has no crossing

**Conclusion**: `d_{m+l-n}^q(y) = w`.

**Proof sketch**:
1. Find representative [x] of x such that p[x] ∈ {z} and f[x] ∈ {y} (using no-crossing from (3))
2. By (5), (2), and Prop 2.10(2): Fil(qf[x]) ≥ s + n + k
3. Since diagram commutes on E∞: Fil(gp[x]) = Fil(qf[x]) ≥ s + n + k
4. By (4), (1), and Prop 2.10: gp[x] ∈ {w}
5. Therefore qf[x] ∈ {w}, and by (2) there is a q-extension from y to w

### Corollary 2.15

Same setup, same hypotheses but WITHOUT the k parameter:
1. `d_n^f(x) = y`
2. `d_m^p(x) = z`
3. Differential in (1) or (2) has no crossing
4. `d_l^g(z) = w`, and has no crossing

**Conclusion**: `d_{m+l-n}^q(y) = w`.

Special case of Thm 2.12 with the d^g differential having no crossing at all.

### Corollary 2.16: Triangle case

```
V₁ --f--> V₂
 \         |q
  p\       v
    \-->  V₃
```

Hypotheses: n, m ≥ 0:
1. `d_n^f(x) = y`
2. `d_m^p(x) = z`
3. Differential in (1) or (2) has no crossing

**Conclusion**: `d_{m-n}^q(y) = z`.

*Proof*: Special case of Cor 2.15 with V₃ = V₄ and g = id.

### Corollary 2.17: Composition case

```
V₁ --p--> V₃
 \         |g
  q\       v
    \-->  V₄
```

Hypotheses: m, l ≥ 0:
1. `d_m^p(x) = z`
2. `d_l^g(z) = w`, and has no crossing

**Conclusion**: `d_{m+l}^q(x) = w`.

*Proof*: Special case of Cor 2.15 with V₁ = V₂ and f = id.

### Corollary 2.18: Induced map on ESS pages

Same square. If `ᵖE₀ = ᵖE_r` and `ᵍE₀ = ᵍE_r` for some r ≥ 0, then
`(d_r^p, d_r^q)` induces a map from the f-ESS to the g-ESS.

*Proof*: The E₀ = E_r conditions force d_r^p, d_r^q to have no crossings. Apply Cor 2.15 to get compatibility at each page level, then induct.

### Corollary 2.19: Null composition

If g∘f is null-homotopic and `d_n^f(x) = y`, then y is a permanent cycle in the g-ESS:
`d_m^g(y) = 0` for all m ≥ 0.

*Proof 1*: Apply Cor 2.15 to the diagram with V₃ = 0.
*Proof 2*: By Prop 2.5, ∃ [x] with f([x]) ∈ {y}. Then g(f([x])) = 0, so y survives all g-differentials.

## Formalization Strategy

1. Define `HomotopyCommSquare` for converging spectral sequences (four SS morphisms with commutativity)
2. Axiomatize Theorem 2.12 — the most general form
3. Derive Corollaries 2.15–2.19 from Theorem 2.12 (or axiomatize individually)
4. Use NoCrossing/NoCrossingRange from Crossing.lean
5. Use ESSData/ESSDifferential from Extension.lean

The key challenge is that these results are about the interplay of four ESS differentials. The formalization should bundle the four convergent spectral sequences and their morphisms.

## Dependencies
- `KIPBase.SpectralSequence.Basic`
- `KIPBase.SpectralSequence.Convergence`
- `KIPBase.SpectralSequence.Crossing`
- `KIPBase.SpectralSequence.Extension` (for ESS structure, Prop 2.5, Prop 2.10)
