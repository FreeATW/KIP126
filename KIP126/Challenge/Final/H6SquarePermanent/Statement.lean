import KIP126.Challenge.Near126.OnlyD12.Statement

/-! Exact conditional endpoint statement for the permanent `h₆²` class. -/
namespace KIP126.Challenge.Final.H6SquarePermanent

open KIP126.Challenge.Near126.OnlyD12
open KIP126.Classical.Adams
open KIP126.Kervaire
open KIP126.Synthetic.SpectralSequence

structure Input
    {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier] where
  near : KIP126.Challenge.Near126.OnlyD12.Input
    (C := C) (S := S) (A := A) (Carrier := Carrier)
  noD12 : ¬ (near.d12Value = near.d12Target ∧ near.d12Value ≠ 0)

/-- The endpoint theorem consumes the near-126 no-`d₁₂` branch and concludes
permanence of the same `h₆²` class recorded by the input context. -/
def statement {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier]
    (I : Input (C := C) (S := S) (A := A) (Carrier := Carrier)) : Prop :=
  I.near.context.h6Permanent

end KIP126.Challenge.Final.H6SquarePermanent
