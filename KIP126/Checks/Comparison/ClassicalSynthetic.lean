import KIP126.Def.Comparison.ClassicalSynthetic.Proofs
import KIP126.External.Claims

/-!
# AIM-6 classical--synthetic regression

The examples below consume the existing catalogue wrapper and check the
concrete grading, page, and differential interfaces without postulating a
particular synthetic spectrum.
-/

namespace KIP126.Comparison.ClassicalSynthetic.Regression

open CategoryTheory
open KIP126.Classical.Adams
open KIP126.External
open KIP126.Synthetic.SpectralSequence

example : syntheticAdamsPageLevel.firstPage = 2 := rfl
example (r : ℕ) : syntheticAdamsPageLevel.page r = r := rfl
example (r : ℕ) :
    syntheticAdamsPageLevel.cycleLevel r =
      syntheticAdamsPageLevel.quotientExponent r :=
  syntheticAdamsPageLevel.cycleLevel_eq_quotientExponent r

example {classical : ClassicalAdamsSpectralSequence}
    {synthetic : SyntheticAdamsSS}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w r : ℤ) (hr : 2 ≤ r) (b : Bidegree) :
    (classical.page r).d b (classicalAdamsTarget r.toNat b) ≫
        (comparison.map w r hr).f (classicalAdamsTarget r.toNat b) =
      (comparison.map w r hr).f b ≫
        (fixedWeightPage synthetic.sequence w r hr).d b
          (classicalAdamsTarget r.toNat b) :=
  comparison.differential_comm w r hr b

example (r : ℕ) (i : Tridegree) :
    (syntheticAdamsShape r).Rel i (syntheticAdamsTarget r i) :=
  syntheticAdamsShape_rel r i

example (A : SyntheticAdamsSS) (r : ℕ) (i : Tridegree)
    (hr : 2 ≤ r)
    (h : (A.sequence.page (r : ℤ)).d i (syntheticAdamsTarget r i) ≠ 0) :
    i.2.2 = (syntheticAdamsTarget r i).2.2 :=
  weightPreserving_differential A r hr i h

example (A : SyntheticAdamsSS) (i j : Tridegree) :
    A.lambdaMap i ≫ A.E₂.d (lambdaTarget i) (lambdaTarget j) =
      A.E₂.d i j ≫ A.lambdaMap j :=
  A.lambdaMap_comm i j

example : forgetWeight syntheticH₄Degree = classicalH₄Degree :=
  synthetic_h₄_degree_forgets

example : syntheticH₄TargetDegree =
    lambdaTarget syntheticH₀H₃SquaredDegree :=
  synthetic_h₄_target_is_lambda_target

example :
    (externalClaimLedger.lookup .adamsOneLine).owner =
      `KIP126.Classical.adamsOneLineDifferentials := rfl

end KIP126.Comparison.ClassicalSynthetic.Regression
