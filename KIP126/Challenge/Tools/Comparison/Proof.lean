import KIP126.Challenge.Tools.Comparison.Statement
import KIP126.Def.Comparison.ClassicalSynthetic.Proofs

namespace KIP126.Comparison.ClassicalSynthetic

open CategoryTheory
open KIP126.Classical.Adams
open KIP126.Synthetic.SpectralSequence

theorem ReindexedSpectralSequenceMap.differential_comm
    {classical : ClassicalAdamsSpectralSequence}
    {synthetic : SyntheticAdamsSS}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w r : ℤ) (hr : 2 ≤ r) (b : Bidegree) :
    (classical.page r).d b (classicalAdamsTarget r.toNat b) ≫
        (comparison.map w r hr).f (classicalAdamsTarget r.toNat b) =
      (comparison.map w r hr).f b ≫
        (fixedWeightPage synthetic.sequence w r hr).d b
          (classicalAdamsTarget r.toNat b) := by
  exact (comparison.map w r hr).comm b (classicalAdamsTarget r.toNat b) |>.symm

theorem sourcePageMap_differential_naturality
    {classical : ClassicalAdamsSpectralSequence}
    {synthetic : SyntheticAdamsSS}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w r : ℤ) (hr : 2 ≤ r) (b : Bidegree) :
    (classical.page r).d b (classicalAdamsTarget r.toNat b) ≫
        (comparison.map w r hr).f (classicalAdamsTarget r.toNat b) =
      (comparison.map w r hr).f b ≫
        (fixedWeightPage synthetic.sequence w r hr).d b
          (classicalAdamsTarget r.toNat b) :=
  comparison.differential_comm w r hr b

end KIP126.Comparison.ClassicalSynthetic

namespace KIP126.Challenge.Tools.Comparison

/-- The page maps are chain maps, so differential naturality is already proved
at this structural level. This does not assert the open h₄ comparison. -/
theorem differentialNaturality : DifferentialNaturality := by
  intro classical synthetic comparison w r hr b
  exact comparison.differential_comm w r hr b

end KIP126.Challenge.Tools.Comparison
