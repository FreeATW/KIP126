import KIP126.Def.Kervaire.SphereAdams
import KIP126.External.Literature.Kervaire

/-!
# Theorem 7.3: BJM/BX criterion for every order-two choice

The source criterion and the choice-filtration input are explicit fields of
`AnyChoiceCriterion`; this declaration states the transported mathematical
conclusion over that semantic interface.
-/
namespace KIP126.Challenge.Near126.Thm7_3BJMBX

open KIP126.Kervaire

/-- For every admissible order-two synthetic choice `theta5`, `h₆²` survives
exactly when the displayed `lambda eta` square vanishes, and permanence is
equivalent to vanishing in the untruncated sphere. -/
theorem any_choice_criterion [I : AnyChoiceCriterion] :
  ∀ (theta5 : I.Carrier), I.context.isChoice theta5 →
    IsOrderTwo theta5 →
      (∀ (r : ℕ), 1 ≤ r →
        (I.context.h6Survives (r + 3) ↔
          I.context.finiteZero (r + 1)
            (I.context.lambdaEta (I.context.square theta5)))) ∧
      (I.context.is_permanent (I.context.lambdaEta (I.context.square theta5)) ↔
        I.context.untruncatedZero
          (I.context.lambdaEta (I.context.square theta5))) := by
  sorry

end KIP126.Challenge.Near126.Thm7_3BJMBX
