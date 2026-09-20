import KIP126.Solution.Near126.C3NotC5.Statement

/-! The final eta-extension scenario is excluded by the C₃/C₅ interface. -/
namespace KIP126.Solution.Near126.ExcludeEta

open KIP126.Solution.Near126.C3NotC5
open KIP126.Classical.Adams
open KIP126.Kervaire
open KIP126.Synthetic.SpectralSequence

theorem statement {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} {Carrier : Type} [AddCommGroup Carrier]
    (I : KIP126.Solution.Near126.OnlyD12.Input
      (C := C) (S := S) (A := A) (Carrier := Carrier)) :
  (I.near.d6 (I.near.x12684 + I.near.x1268) = 0) →
    ¬ (I.near.lambda3 (I.near.etaAction I.near.h0SquaredX1248) =
      I.near.lambda6H1h4 I.near.h1h4X10912) := by
  sorry

end KIP126.Solution.Near126.ExcludeEta
