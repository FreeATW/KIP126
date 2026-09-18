import KIP126.Def.Comparison.ClassicalSynthetic.Data

/-! The chain-map part of the classical/synthetic page comparison. -/

namespace KIP126.Challenge.Tools.Comparison

open CategoryTheory
open KIP126.Classical.Adams
open KIP126.Synthetic.SpectralSequence
open KIP126.Comparison.ClassicalSynthetic

/-- Every chosen page map commutes with its page differential, in the
classical bidegree and at each fixed synthetic weight. -/
def DifferentialNaturality : Prop :=
  ∀ (classical : ClassicalAdamsSpectralSequence)
    (synthetic : SyntheticAdamsSS)
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w r : ℤ) (hr : 2 ≤ r) (b : Bidegree),
    (classical.page r).d b (classicalAdamsTarget r.toNat b) ≫
        (comparison.map w r hr).f (classicalAdamsTarget r.toNat b) =
      (comparison.map w r hr).f b ≫
        (fixedWeightPage synthetic.sequence w r hr).d b
          (classicalAdamsTarget r.toNat b)

end KIP126.Challenge.Tools.Comparison
