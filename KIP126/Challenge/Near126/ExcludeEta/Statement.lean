import KIP126.Challenge.Near126.C3NotC5.Statement

/-! The final eta-extension scenario is excluded by the C₃/C₅ interface. -/
namespace KIP126.Challenge.Near126.ExcludeEta

open KIP126.Challenge.Near126.C3NotC5
open KIP126.Classical.Adams
open KIP126.Kervaire
open KIP126.Synthetic.SpectralSequence

def statement {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier]
    (I : KIP126.Challenge.Near126.OnlyD12.Input
      (C := C) (S := S) (A := A) (Carrier := Carrier)) : Prop :=
  (I.near.d6 (I.near.x12684 + I.near.x1268) = 0) →
    ¬ (I.near.lambda3 (I.near.etaAction I.near.h0SquaredX1248) =
      I.near.lambda6H1h4 I.near.h1h4X10912)

end KIP126.Challenge.Near126.ExcludeEta
