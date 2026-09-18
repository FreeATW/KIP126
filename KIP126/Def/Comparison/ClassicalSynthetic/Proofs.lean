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

end KIP126.Comparison.ClassicalSynthetic
