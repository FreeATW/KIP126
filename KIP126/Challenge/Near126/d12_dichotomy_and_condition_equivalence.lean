import KIP126.Def.Kervaire.SphereAdams

/-! Exact open statement for Proposition 7.8. -/
namespace KIP126.Challenge.Near126.OnlyD12

open KIP126.Kervaire

/-- The two alternatives are exclusive and exhaustive, and the nonzero
`d₁₂` alternative is equivalent to the three displayed conditions. -/
theorem d12_dichotomy_and_condition_equivalence [D : Near126Adams] :
  ((D.h6_square_isPermanent ∧
      ¬ D.d12_differential_is_nonzero) ∨
    (D.d12_differential_is_nonzero ∧
      ¬ D.h6_square_isPermanent)) ∧
    (D.d12_differential_is_nonzero ↔ D.c3 ∧ D.c4 ∧ D.c5) := by
  sorry

end KIP126.Challenge.Near126.OnlyD12
