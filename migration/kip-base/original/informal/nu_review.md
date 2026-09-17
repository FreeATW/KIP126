# Nu.lean — Reviewer refinements (Round 11)

## Task 1: Convert `nu_shift_biShift` from `theorem ... sorry` to `axiom`

**Current** (line 55):
```lean
theorem nu_shift_biShift (n : ℤ) (X : 𝒮) :
  (nu 𝒮 Syn).obj ((shiftFunctor 𝒮 n).obj X) ≅
    (SyntheticCategory.biShift (n, n)).obj ((nu 𝒮 Syn).obj X) := by sorry
```

This was previously attempted and documented as a dead end (ℤ-induction negative case too complex). **Convert to `axiom`** — the statement is mathematically correct.

## Task 2: Convert `nu_cofiber_ses_cohomological` from `theorem ... sorry` to `axiom`

**Current** (line 80):
```lean
theorem nu_cofiber_ses_cohomological ... := by sorry
```

The proof would require composing `nu_cofiber_ses` with universal coefficients (`universal_coefficient` in Cohomology.lean). The key difficulty: we need to convert a cohomological exactness hypothesis to a homological one via UCT, but our UCT is stated as an `AddEquiv`, not in a form that directly transforms `Function.Exact` statements. **Convert to `axiom`.**

## Summary

Both changes are converting `theorem ... sorry` to `axiom` declarations. This:
- Removes 2 sorries from the count
- Makes the axiom inventory honest
- Preserves the exact same type signatures
- No downstream impact (both are only used via their types, not their proofs)
