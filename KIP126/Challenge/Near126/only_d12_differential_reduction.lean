import KIP126.Def.Kervaire.SphereAdams

/-! Exact candidate-reduction interface for the near-126 differential search. -/
namespace KIP126.Challenge.Near126.CandidateReduction

open KIP126.Kervaire

/-- Every differential length other than `12` is excluded; the remaining
candidate is exactly the displayed `d₁₂` differential. -/
theorem only_d12_differential_reduction [D : Near126Adams] :
  (∀ r : ℕ, r ≠ 12 → ¬ D.differential r) ∧
    (D.differential 12 ↔ D.d12_differential_is_nonzero) ∧
    (¬ D.differential 12 ↔ D.h6_square_isPermanent) := by
  sorry

end KIP126.Challenge.Near126.CandidateReduction
