# Informal Guide: Spectral Sequences (§1)

This covers all files in `KIPBase/SpectralSequence/`.

## Mathlib Infrastructure Available

- `GradedObject β C` = `β → C` (functor from index type to category). File: `Mathlib.CategoryTheory.GradedObject`
- Abelian categories: `Mathlib.CategoryTheory.Abelian.Basic`
- Homological complexes: `Mathlib.Algebra.Homology.HomologicalComplex`
- Kernels, cokernels, images: `Mathlib.CategoryTheory.Limits.Shapes.Kernels` etc.
- **No spectral sequence API exists in Mathlib** — must build from scratch.

## Key Design Decisions

### Grading Convention
Use `GradedObject (ι → ℤ) C` for `ι`-graded objects (where `ι = Fin n` for n-grading).
For bigraded objects (Adams SS), use `ℤ × ℤ` directly.
For trigraded objects (synthetic), use `ℤ × ℤ × ℤ`.

### Spectral Sequence Structure

```
structure SpectralSequence (C : Type*) [Category C] [Abelian C]
    (ι : Type*) [AddCommGroup ι] where
  page : ℤ → GradedObject ι C          -- E_r for r ≥ r₀
  differential : ∀ r, page r ⟶ page r  -- d_r (as graded morphism)
  diff_deg : ℤ → ι                      -- degree of d_r
  diff_sq : ∀ r, differential r ≫ differential r = 0
  iso_next : ∀ r, homology(page r, differential r) ≅ page (r + 1)
  r₀ : ℤ                                -- starting page
```

Since Mathlib doesn't have homology of graded objects with graded differentials, the prover may need to define this componentwise: for each index k, take `kernel (d_r k) / image (d_r (k - deg))`.

### Alternative: Simpler Axiomatized Approach
Since this is foundational infrastructure and the project is about extensions/synthetic spectra, consider axiomatizing spectral sequences more abstractly:

```
class SpectralSequence (C : Type*) [Category C] [Abelian C] (ι : Type*) where
  Page : ℤ → ι → C
  d : (r : ℤ) → (k : ι) → Page r k ⟶ Page r (k + diffDeg r)
  diffDeg : ℤ → ι
  d_comp_d : ∀ r k, d r k ≫ d r (k + diffDeg r) = 0
  pageIso : ∀ r k, -- ker(d_r^k) / im(d_r^{k-deg}) ≅ E_{r+1}^k
    sorry
```

## File-by-File Guide

### Basic.lean (§1.1)
Define:
- `GradedMorphism C ι (deg : ι)` — morphism of graded objects of given degree
- `SpectralSequence C ι` — the main structure (pages, differentials, d²=0, page isomorphisms)
- `EInfty` — the E∞-page (permanent cycles / permanent boundaries)

The E∞-page requires limits/colimits. For now, axiomatize it as a field or define it for the degenerate case (SS degenerates at finite page).

### Convergence.lean (§1.2)
Define:
- `Filtration A` — decreasing filtration on an (n-1)-graded object: `ℤ → Subobject (A k)` with monotonicity
- `AssociatedGraded` — `gr^r A^k = F^r A^k / F^{r+1} A^k`
- `Converges E A` — E∞ ≅ gr A (up to linear reindexing of grading)
- `StemDegree`, `FiltrationDegree` — components of the grading
- `Detects y x` — element y ∈ E∞ detects x ∈ A
- Propositions: detect_zero, detect_difference (with `sorry`)

### Filtered.lean (§1.3)
Define:
- `FilteredChainComplex C` — chain complex with compatible decreasing filtration
- `filteredSS` — associated spectral sequence (axiom: state its existence with E₀ page)
- `filteredConvergence` — convergence to homology under bounded filtration (axiom)
- Functoriality statement

### Crossing.lean (§1.4)
Define:
- The extension spectral sequence for a map `f : X → Y`:
  `ExtensionSS f` — SS from filtering `0 → π_*X → π_*Y → 0` by Adams filtration
- `Crossing` — Definition 1 from blueprint: d' crosses d when d' is nontrivial, same stem with strictly higher filtration
- `NoCrossing` — negation with the characterization from Prop. no-crossing-iff
- `HasCrossingHitsAF` — crossing hits Adams filtration p

### Extension.lean (§1.5)
Define:
- `fExtension x y` — there is an f-extension from x to y (d_n^f(x) = y)
- `EssentialExtension` — y is nontrivial in the E_n-page
- Characterization propositions (with `sorry`)
- `fourSpectra` theorem — the main tool (Theorem from blueprint, with `sorry`)
- Corollaries: `triangleMap`, `compositionExt`, `essNaturality`, `compositionZero`

### Commutativity.lean (§1.6)
State the commutativity results (Prop 2.12 and corollaries) as axioms or theorems with `sorry`.
This is the most advanced part of §1 — may need §2 infrastructure first.
