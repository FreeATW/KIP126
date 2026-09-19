import KIP126.Challenge.Near126.OnlyD12.Statement

/-! Open existential-to-universal transport statements for C₄ and C₅. -/
namespace KIP126.Challenge.Near126.Conditions

open KIP126.Challenge.Near126.OnlyD12
open KIP126.Classical.Adams
open KIP126.Kervaire
open KIP126.Synthetic.SpectralSequence

structure Input
    {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier] where
  near : OnlyD12.Input (C := C) (S := S) (A := A) (Carrier := Carrier)
  c4At : Carrier → Prop
  c5At : Carrier → Prop

def statement {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier]
    (I : Input (C := C) (S := S) (A := A) (Carrier := Carrier)) : Prop :=
  ((I.c4At I.near.context.sourceChoice ↔
      ∀ θ, I.near.context.isChoice θ → I.c4At θ) ∧
    (I.c5At I.near.context.sourceChoice ↔
      ∀ θ, I.near.context.isChoice θ → I.c5At θ))

end KIP126.Challenge.Near126.Conditions
