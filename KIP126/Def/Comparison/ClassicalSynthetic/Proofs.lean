import KIP126.Def.Comparison.ClassicalSynthetic.Data

namespace KIP126.Comparison.ClassicalSynthetic

open CategoryTheory
open KIP126.Classical.Adams
open KIP126.Synthetic.SpectralSequence

theorem forgetWeight_page_shape (r : ℕ) (i : Tridegree) :
    (syntheticAdamsShape r).Rel i (syntheticAdamsTarget r i) :=
  syntheticAdamsShape_rel r i

theorem forgetWeight_differential_degree (r : ℕ) (i : Tridegree) :
    forgetWeight (syntheticAdamsTarget r i) =
      classicalAdamsTarget r (forgetWeight i) :=
  forgetWeight_add_shift r i

theorem synthetic_h₄_degree_forgets :
    forgetWeight syntheticH₄Degree = classicalH₄Degree := by
  simp

theorem synthetic_h₄_target_is_lambda_target :
    syntheticH₄TargetDegree = lambdaTarget syntheticH₀H₃SquaredDegree := rfl

/-- Every chosen page map commutes with its page differential. -/
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

/-- The source page map is a chain map at every fixed synthetic weight. -/
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
