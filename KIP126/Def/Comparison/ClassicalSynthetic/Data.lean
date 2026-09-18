import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.Def.Synthetic.AdamsSequence.Data
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Field.ZMod

/-!
# Classical--synthetic comparison basics

The comparison is heterogeneous only in its grading index.  Its page maps
still target the same Mathlib page objects, and the compatibility fields are
specific to the concrete forget-weight use case.
-/

namespace KIP126.Comparison.ClassicalSynthetic

open CategoryTheory
open KIP126.Classical.Adams
open KIP126.Synthetic.SpectralSequence

structure ReindexedSpectralSequenceMap
    (classical : ClassicalAdamsSpectralSequence)
    (synthetic : SyntheticAdamsSS) where
  map : ∀ (w : ℤ) (r : ℤ) (hr : 2 ≤ r),
    (classical.page r) ⟶ fixedWeightPage synthetic.sequence w r hr
  pagePassage : ∀ (w : ℤ) (r : ℤ) (hr : 2 ≤ r) (b : Bidegree),
    (fixedWeightPage synthetic.sequence w r hr).homology b ≅
      (fixedWeightPage synthetic.sequence w (r + 1) (by omega)).X b
  page_passage_comm : ∀ (w : ℤ) (r : ℤ) (hr : 2 ≤ r) (b : Bidegree),
    HomologicalComplex.homologyMap (map w r hr) b ≫
        (pagePassage w r hr b).hom =
      (classical.iso r (r + 1) b rfl hr).hom ≫
        (map w (r + 1) (by omega)).f b

def sourcePageMap
    {classical : ClassicalAdamsSpectralSequence}
    {synthetic : SyntheticAdamsSS}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w : ℤ) (r : ℤ) (hr : 2 ≤ r) (b : Bidegree) :
    (classical.page r).X b ⟶ (fixedWeightPage synthetic.sequence w r hr).X b :=
  (comparison.map w r hr).f b

abbrev classicalH₄Degree : Bidegree := (1, 16)
abbrev classicalH₀H₃SquaredDegree : Bidegree := (3, 17)
abbrev syntheticH₄Degree : Tridegree := nuDegree classicalH₄Degree
abbrev syntheticH₀H₃SquaredDegree : Tridegree :=
  nuDegree classicalH₀H₃SquaredDegree
abbrev syntheticH₄TargetDegree : Tridegree :=
  lambdaTarget syntheticH₀H₃SquaredDegree

end KIP126.Comparison.ClassicalSynthetic
