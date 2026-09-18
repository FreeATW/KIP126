import KIP126.Def.ClassicalAdams.Page.Data
import KIP126.Def.StableHomotopy.Context.Data
import KIP126.Def.Algebra.Completion.Data
import KIP126.Def.Algebra.Filtration.Predicates
import Mathlib.Algebra.Category.Grp.Abelian

/-! Chosen classical Adams sequence and convergence data. -/
namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

/-- Explicit convergence data for a chosen Adams sequence. The propositions
are witnesses supplied by a concrete construction, not global assumptions. -/
structure ClassicalAdamsConvergence (E : ClassicalAdamsSpectralSequence) where
  abutment : CategoryTheory.GradedObject Bidegree F2ModuleCat
  filtration : KIP126.Core.Algebra.Filtration abutment
  filtrationDegree : Bidegree → ℤ
  comparisonPage : Bidegree → ℤ
  comparisonPage_ge_two : ∀ b, 2 ≤ comparisonPage b
  pageComparison : ∀ b,
    (E.page (comparisonPage b) (comparisonPage_ge_two b)).X b ≅
      filtration.associatedGraded (filtrationDegree b) b
  complete : ∀ b, KIP126.Core.Algebra.Filtration.CompletionWitness filtration b
  /-- The strong degreewise eventual-top predicate named `IsExhaustive`. -/
  exhaustive : filtration.IsExhaustive
  /-- Degreewise eventual-bottom, stronger than separatedness. -/
  eventuallyZero : filtration.IsEventuallyZero

/-- A chosen classical Adams sequence for one spectrum. -/
structure ClassicalAdamsSS (stable : StableHomotopyContext)
    (X : stable.Spectrum) where
  sequence : ClassicalAdamsSpectralSequence
  convergence : ClassicalAdamsConvergence sequence

/-- The stem represented by an Adams bidegree `(s,t)`. -/
def adamsStem (b : Bidegree) : ℤ := b.2 - b.1

/-- The underlying additive group of one component of a classical Adams page. -/
abbrev UnderlyingAdamsPage (E : ClassicalAdamsSpectralSequence) (r : ℤ)
    (hr : 2 ≤ r) (b : Bidegree) : AddCommGrpCat :=
  (forget₂ F2ModuleCat AddCommGrpCat).obj ((E.page r hr).X b)

/-- The `2`-complete stable homotopy groups attached to every spectrum in a
chosen stable-homotopy context. -/
structure TwoCompleteStableHomotopy (stable : StableHomotopyContext) where
  groups : stable.Spectrum → CategoryTheory.GradedObject ℤ AddCommGrpCat

end KIP126.Classical.Adams
