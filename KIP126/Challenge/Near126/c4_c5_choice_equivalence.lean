import KIP126.Def.Kervaire.SphereAdams

/-! Open existential-to-universal transport statements for C₄ and C₅. -/
namespace KIP126.Challenge.Near126.Conditions

open KIP126.Kervaire

/-- The distinguished source choice satisfies `C₄` and `C₅` exactly when
all admissible order-two choices satisfy the same conditions. -/
theorem c4_c5_choice_equivalence [I : ChoiceConditions] :
  ((I.c4_at I.context.sourceChoice ↔
      ∀ θ, I.context.isChoice θ → I.c4_at θ) ∧
    (I.c5_at I.context.sourceChoice ↔
      ∀ θ, I.context.isChoice θ → I.c5_at θ)) := by
  sorry

end KIP126.Challenge.Near126.Conditions
