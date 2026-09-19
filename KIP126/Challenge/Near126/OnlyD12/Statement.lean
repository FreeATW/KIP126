import KIP126.Def.Kervaire.Setup.Data
import KIP126.Def.Kervaire.Theta5.Proofs

/-! Exact open statement for Proposition 7.8. -/
namespace KIP126.Challenge.Near126.OnlyD12

open KIP126.Kervaire
open KIP126.Classical.Adams
open KIP126.External
open KIP126.Synthetic.SpectralSequence

structure Input
    {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier] where
  near : Near126Input S A
  conditions : Near126Conditions near
  context : Theta5ChoiceContext (Carrier := Carrier)
  criterion : CataloguedExternalResult (BJM_BXCriterion context)
  order : CataloguedExternalResult (Theta5OrderData context)
  d12Value : Carrier
  d12Target : Carrier
  d12Value_eq : d12Value = context.deltaH6
  d12Target_eq : d12Target = context.lambdaEta (context.square context.sourceChoice)

/-- The two alternatives are exclusive and exhaustive, and the nonzero
`d₁₂` alternative is equivalent to the three displayed conditions. -/
def statement {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier]
    (I : Input (C := C) (S := S) (A := A) (Carrier := Carrier)) : Prop :=
  let c3 : Prop := I.near.d6 (I.near.x12684 + I.near.x1268) = 0
  let c4 : Prop :=
    I.near.theta5Square = I.near.lambda6 I.near.h0SquaredX1248 ∧
      I.near.theta5Square ≠ 0
  let c5 : Prop :=
    I.near.lambda3 (I.near.etaAction I.near.h0SquaredX1248) =
      I.near.lambda6H1h4 I.near.h1h4X10912
  ((I.context.h6Permanent ∧
      ¬ (I.d12Value = I.d12Target ∧ I.d12Value ≠ 0)) ∨
    ((I.d12Value = I.d12Target ∧ I.d12Value ≠ 0) ∧
      ¬ I.context.h6Permanent)) ∧
    ((I.d12Value = I.d12Target ∧ I.d12Value ≠ 0) ↔
      (c3 ∧ c4 ∧ c5))

end KIP126.Challenge.Near126.OnlyD12
