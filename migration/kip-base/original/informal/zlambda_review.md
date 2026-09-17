# Synthetic/Basic.lean — Reviewer refinement (Round 11)

## `zlambda_enrichment`: Convert `theorem ... sorry` to `axiom`

**Current** (line 155):
```lean
theorem zlambda_enrichment ... : EnrichedCategory (ModuleCat (Polynomial ℤ)) Syn := by sorry
```

**Analysis**: The reviewer gives a 3-step proof strategy:
- (a) ℤ-enrichment from Preadditive — available via `AddCommGroup.intModule`
- (b) λ-action on Hom(X,Y) — **BLOCKED**: requires defining a ℤ-linear endomorphism of `(X ⟶ Y)` from `lam`. `lam.app X : biShift(0,-1).obj X ⟶ X` does NOT give an endomorphism of `Hom(X,Y)`. Would need biShift fully faithful or closed enrichment structure not available.
- (c) Polynomial.aeval — standard Mathlib, but depends on (b)

Step (b) is the hard part and was previously identified as blocked on Mathlib infrastructure. The `informal/lambdaPow.md` file has a detailed analysis showing this.

**Decision**: Convert to `axiom`. The statement `EnrichedCategory (ModuleCat (Polynomial ℤ)) Syn` is correct mathematically. The Lean 4/Mathlib gap in step (b) is genuine — we cannot construct a ℤ-linear endomorphism of Hom-sets from a natural transformation `biShift(0,-1) ⟶ 𝟭 Syn` without additional enrichment machinery.

This removes 1 sorry and adds 1 axiom.
