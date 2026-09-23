import KIP126.Def.ClassicalAdams.Convergence.Predicates

namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

/-- Strong convergence data for the Adams sequence of the specified spectrum.
Every page after `stablePage b` is identified with the associated graded of
the `2`-complete stable homotopy of that same spectrum, and the identifications
commute with Mathlib's page-passage isomorphisms. -/
structure StrongClassicalAdamsConvergence {stable : StableHomotopyContext}
    (π₂ : TwoCompleteStableHomotopy stable) (X : stable.Spectrum)
    (E : ClassicalAdamsSpectralSequence) where
  filtration : KIP126.Core.Algebra.Filtration (π₂.groups X)
  stablePage : Bidegree → ℤ
  stablePage_ge_two : ∀ b, 2 ≤ stablePage b
  pageHomologyIso : ∀ (b : Bidegree) (r : ℤ) (hr : stablePage b ≤ r),
    (E.page r ((stablePage_ge_two b).trans hr)).homology b ≅
      (E.page r ((stablePage_ge_two b).trans hr)).X b
  pageComparison : ∀ (b : Bidegree) (r : ℤ) (hr : stablePage b ≤ r),
    UnderlyingAdamsPage E r ((stablePage_ge_two b).trans hr) b ≅
      filtration.associatedGraded b.1 (adamsStem b)
  pagePassage_coherent : ∀ (b : Bidegree) (r : ℤ) (hr : stablePage b ≤ r),
    (forget₂ F2ModuleCat AddCommGrpCat).map
        (pageHomologyIso b r hr).inv ≫
      (forget₂ F2ModuleCat AddCommGrpCat).map
        (E.iso r (r + 1) b rfl ((stablePage_ge_two b).trans hr)).hom ≫
      (pageComparison b (r + 1) (hr.trans (by omega))).hom =
        (pageComparison b r hr).hom
  complete : ∀ n,
    KIP126.Core.Algebra.Filtration.CompletionWitness filtration n
  /-- The strong degreewise eventual-top predicate named `IsExhaustive`. -/
  exhaustive : filtration.IsExhaustive
  separated : IsAdamsFiltrationSeparated filtration

/-- A classical Adams slice whose strong-convergence data is bound to the
specified spectrum.  The extra convergence field prevents reusing the same
value at an unrelated spectrum even though the legacy page-only slice is
retained for API compatibility. -/
structure SpectrumBoundClassicalAdamsSS {stable : StableHomotopyContext}
    (π₂ : TwoCompleteStableHomotopy stable) (X : stable.Spectrum) where
  pageSlice : ClassicalAdamsSS stable X
  strongConvergence :
    StrongClassicalAdamsConvergence π₂ X pageSlice.sequence

end KIP126.Classical.Adams
