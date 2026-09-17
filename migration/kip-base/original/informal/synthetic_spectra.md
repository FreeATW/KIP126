# Informal Guide: HF₂-Synthetic Spectra (§3)

This covers all files in `KIPBase/Synthetic/`.

## Mathlib Infrastructure Available

Same as §2 — triangulated categories, model categories, etc.
Everything in §3 is axiomatized on top of §1 (spectral sequences) and §2 (stable homotopy).

## Overall Approach

Synthetic spectra form an axiomatic framework. The key idea is:
- `Syn` is another pretriangulated category (axiomatized directly, not via model categories)
- There's a functor `ν : 𝒮 → Syn` from spectra to synthetic spectra
- Synthetic spectra have a **bigrading** (stem, weight) instead of single grading
- The element `λ ∈ π_{0,-1}(S^{0,0})` parametrizes a deformation from algebra to topology
- The synthetic Adams SS has `E₂ ≅ classical E₂ ⊗ F₂[λ]` (rigidity)

## File-by-File Guide

### Basic.lean (§3.1)
Define the synthetic spectra category axiomatically:

```
class SyntheticCategory (Syn : Type*) extends
    Category Syn, HasShift Syn ℤ, Pretriangulated Syn where
  -- Bigraded suspension: Σ^{m,n}
  biShift : ℤ × ℤ → Syn ⥤ Syn
  biShift_comp : ∀ a b, biShift a ⋙ biShift b ≅ biShift (a + b)
  -- Σ^{1,0} = suspension
  susp_is_shift : biShift (1, 0) ≅ shiftFunctor Syn (1 : ℤ)
  -- λ : Σ^{0,-1} → Id
  lambda : biShift (0, -1) ⟶ 𝟭 Syn   -- natural transformation
```

Define:
- `XModLambda (X : Syn) (n : ℕ) : Syn` — cofiber of λⁿ (X/λⁿ)
- `hSyn` — homotopy category (if needed, or just work in Syn directly)
- Z[λ]-module enrichment on hSyn

### Sphere.lean (§3.2)
Define:
- `S₀₀ : Syn` — the synthetic sphere S^{0,0}
- `Smn (m n : ℤ) : Syn` — bigraded spheres `Σ^{m,n} S^{0,0}`
- `πmn (m n : ℤ) (X : Syn) : AddCommGroup` — bigraded homotopy `[S^{m,n}, X]`
- Suspension invariance: `πmn m n X ≅ πmn (m+k) (n+l) (Σ^{k,l} X)` (axiom)
- Z[λ]-module structure on `π_{*,*}`

### Adams.lean (§3.3)
Define:
- `SynAdamsSS (X : Syn) : SpectralSequence ...` — synthetic Adams SS (3-graded)
- Trigrading `(s, t, w)`, differentials `d_r : E_r^{s,t,w} → E_r^{s+r,t+r-1,w}`
- Adams filtration on `π_{*,*} X`
- Convergence (axiom)
- Lives in Z[λ]-module category

### Nu.lean (§3.4)
Define:
- `nu : 𝒮 ⥤ Syn` — the ν functor
- Condition for preserving distinguished triangles (Axiom/Prop from blueprint §3.1):
  `ν` preserves cofiber sequence iff HF₂-homology sequence is short exact
- `nuSusp : ν(ΣX) ≅ Σ^{1,1} ν(X)` — compatibility with suspension
- Comparison map `Σ(νX) → ν(ΣX)` is λ

### Rigidity.lean (§3.5)
State the key rigidity axioms:
- **Rigidity theorem** (Axiom, BHS Theorem A.8):
  `SynAdamsSS(νX).E₂ ≅ ClassicalAdams(X).E₂ ⊗ F₂[λ]`
  with differential correspondence: classical `d_r(x)=y` gives synthetic `d_r(x)=λ^{r-1}·y`
- **λ-Bockstein** (Axiom, BHS Theorem A.1):
  Synthetic Adams SS ≅ λ-Bockstein SS
  `E₂^{s,t}(X) ≅ π_{t-s,t}(νX/λ)`
- **E∞ computation** (Prop):
  `E∞^{s,t,w}(νX) ≅ Z∞^{s,t}(X) / B_{1+t-w}^{s,t}(X)` for t ≥ w
- **E∞ for νX/λʳ** (Prop):
  `E∞^{s,t,w}(νX/λʳ) ≅ Z_{r-t+w}^{s,t}(X) / B_{1+t-w}^{s,t}(X)` for 0 ≤ t-w < r

### Lift.lean (§3.6)
Define:
- **Synthetic lift** (Axiom, BHS Lemma 9.15):
  If AF(f) = k, then νf factors through λᵏ: there exists `f̃ : Σ^{0,k}νX → νY` with `νf = λᵏ · f̃`
- Adams filtration = λ-Bockstein filtration (Axiom §3.16)
- Canonical λ-division for AF=1 maps (§3.17)
- `ê(f)` notation: 0 if AF(f)=0, 1 if AF(f)>0
- `f̂` notation and distinguished triangle of synthetic spectra (Prop §3.19, §3.20):
  Given `X → Y → Z → ΣX` with e(f)+e(g)+e(h)=1, get synthetic distinguished triangle
