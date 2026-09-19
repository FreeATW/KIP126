import KIP126.Challenge.Near126.OnlyD12.Statement

/-! Exact candidate-reduction interface for the near-126 differential search. -/
namespace KIP126.Challenge.Near126.CandidateReduction

open KIP126.Challenge.Near126.OnlyD12
open KIP126.Classical.Adams
open KIP126.Kervaire
open KIP126.Synthetic.SpectralSequence

structure Input
    {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier] where
  near : OnlyD12.Input (C := C) (S := S) (A := A) (Carrier := Carrier)
  differential : ℕ → Prop

/- The reduction retains both the exclusion of every other length and the
   exact relation between the remaining length and the displayed target. -/
def statement {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier]
    (I : Input (C := C) (S := S) (A := A) (Carrier := Carrier)) : Prop :=
  (∀ r : ℕ, r ≠ 12 → ¬ I.differential r) ∧
    (I.differential 12 ↔
      (I.near.d12Value = I.near.d12Target ∧ I.near.d12Value ≠ 0)) ∧
    (¬ I.differential 12 ↔ I.near.context.h6Permanent)

end KIP126.Challenge.Near126.CandidateReduction
