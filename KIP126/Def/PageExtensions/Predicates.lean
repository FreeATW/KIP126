import KIP126.Def.PageExtensions.Data

/-!
# Filtration and crossing predicates

These predicates port the mathematical content of KIPBase's crossing
definitions to the page-level Mathlib API.  The target filtration is supplied
by the caller; no page convention or hidden `Z/B` model is introduced here.
-/

namespace KIP126.Def.PageExtensions

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable {E : SpectralSequence C c r₀}

/-- A differential together with the filtration degree of its source. -/
structure DifferentialDatum (E : SpectralSequence C c r₀) where
  page : ℤ
  page_ge : r₀ ≤ page
  source : κ
  target : κ
  filtrationDegree : κ → ℤ
  essential : IsEssentialAt c r₀ E page page_ge source target

namespace DifferentialDatum

abbrev sourceDegree (D : DifferentialDatum E) : ℤ := D.filtrationDegree D.source

end DifferentialDatum

/-- A relation for `D` is crossed by an essential differential whose source is
at a strictly higher filtration and whose target lies no higher than the
target filtration bound. -/
def RelationCrossedBy (D : DifferentialDatum E) {T : C}
    (x : PageElement c r₀ E D.page D.page_ge D.source T)
    (y : PageElement c r₀ E D.page D.page_ge D.target T)
    (_h : DifferentialRelation c r₀ E D.page D.page_ge D.source D.target x y) : Prop :=
  ∃ (a : ℤ) (_ha : 0 < a) (r' : ℤ) (hr' : r₀ ≤ r')
    (source' target' : κ) (x' : PageElement c r₀ E r' hr' source' T)
    (y' : PageElement c r₀ E r' hr' target' T),
    D.filtrationDegree source' = D.sourceDegree + a ∧
      EssentialDifferentialRelation c r₀ E r' hr' source' target' x' y' ∧
      D.filtrationDegree target' ≤ D.sourceDegree + D.page

/-- A differential datum with a crossing landing at the specified filtration. -/
def HasCrossingAt (D : DifferentialDatum E) (p : ℤ) : Prop :=
  ∃ (a : ℤ) (_ha : 0 < a) (r' : ℤ) (hr' : r₀ ≤ r')
    (source' target' : κ),
    D.filtrationDegree source' = D.sourceDegree + a ∧
      IsEssentialAt c r₀ E r' hr' source' target' ∧
      p = D.filtrationDegree target' ∧
      D.filtrationDegree target' ≤ D.sourceDegree + D.page

/-- There is no essential crossing whose target lies in the indicated range. -/
def NoCrossingRange (D : DifferentialDatum E) (p : ℤ) : Prop :=
  ¬ ∃ (a : ℤ) (_ha : 0 < a) (r' : ℤ) (hr' : r₀ ≤ r')
    (source' target' : κ),
    D.filtrationDegree source' = D.sourceDegree + a ∧
      IsEssentialAt c r₀ E r' hr' source' target' ∧
      p ≤ D.filtrationDegree target' ∧
      D.filtrationDegree target' ≤ D.sourceDegree + D.page

/-- No crossing above the first filtration level is the ordinary no-crossing
condition. -/
def NoCrossing (D : DifferentialDatum E) : Prop :=
  NoCrossingRange D (D.sourceDegree + 1)

end KIP126.Def.PageExtensions
