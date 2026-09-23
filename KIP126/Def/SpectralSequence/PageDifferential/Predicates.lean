import KIP126.Def.SpectralSequence.PageDifferential.Data

/-!
# Page-level differential and crossing predicates

These predicates concern ordinary differentials in a Mathlib spectral
sequence.  The target filtration is supplied by the caller; no page convention,
filtered-complex presentation, or paper-specific page extension is hidden here.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable {E : SpectralSequence C c r₀}

namespace MathlibModel

/-- A differential at `(r, source, target)` is essential when its page map is
nonzero. Both indices are explicit, as in Mathlib's page differential API. -/
def IsEssentialAt (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (source target : κ) : Prop :=
  PageDifferential c r₀ E r hr source target ≠ 0

/-- Two generalized page elements are related by the specified page
differential. -/
def DifferentialRelation (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (source target : κ) {T : C}
    (x : PageElement c r₀ E r hr source T)
    (y : PageElement c r₀ E r hr target T) : Prop :=
  x ≫ PageDifferential c r₀ E r hr source target = y

/-- A relation is essential exactly when its target page class is nonzero.
A nonzero differential map alone does not make every one of its values essential. -/
def EssentialDifferentialRelation (E : SpectralSequence C c r₀) (r : ℤ)
    (hr : r₀ ≤ r) (source target : κ) {T : C}
    (x : PageElement c r₀ E r hr source T)
    (y : PageElement c r₀ E r hr target T) : Prop :=
  DifferentialRelation E r hr source target x y ∧
    y ≠ 0

/-- A relation for `D` is crossed by an essential differential whose source is
at a strictly higher filtration and whose target lies no higher than the
target filtration bound. -/
def RelationCrossedBy (D : DifferentialDatum (c := c) (r₀ := r₀) E) {T : C}
    (x : PageElement c r₀ E D.page D.page_ge D.source T)
    (y : PageElement c r₀ E D.page D.page_ge D.target T)
    (_h : DifferentialRelation E D.page D.page_ge D.source D.target x y) : Prop :=
  ∃ (a : ℤ) (_ha : 0 < a) (r' : ℤ) (hr' : r₀ ≤ r')
    (source' target' : κ) (x' : PageElement c r₀ E r' hr' source' T)
    (y' : PageElement c r₀ E r' hr' target' T),
    D.filtrationDegree source' = D.sourceDegree + a ∧
      EssentialDifferentialRelation E r' hr' source' target' x' y' ∧
      D.filtrationDegree target' ≤ D.filtrationDegree D.target

/-- A differential datum with a crossing landing at the specified filtration. -/
def HasCrossingAt (D : DifferentialDatum (c := c) (r₀ := r₀) E) (p : ℤ) : Prop :=
  ∃ (a : ℤ) (_ha : 0 < a) (r' : ℤ) (hr' : r₀ ≤ r')
    (source' target' : κ),
    D.filtrationDegree source' = D.sourceDegree + a ∧
      IsEssentialAt E r' hr' source' target' ∧
      p = D.filtrationDegree target' ∧
      D.filtrationDegree target' ≤ D.filtrationDegree D.target

/-- There is no essential crossing whose target lies in the indicated range. -/
def NoCrossingRange (D : DifferentialDatum (c := c) (r₀ := r₀) E) (p : ℤ) : Prop :=
  ¬ ∃ (a : ℤ) (_ha : 0 < a) (r' : ℤ) (hr' : r₀ ≤ r')
    (source' target' : κ),
    D.filtrationDegree source' = D.sourceDegree + a ∧
      IsEssentialAt E r' hr' source' target' ∧
      p ≤ D.filtrationDegree target' ∧
      D.filtrationDegree target' ≤ D.filtrationDegree D.target

/-- No crossing above the first filtration level is the ordinary no-crossing
condition. -/
def NoCrossing (D : DifferentialDatum (c := c) (r₀ := r₀) E) : Prop :=
  NoCrossingRange D (D.sourceDegree + 1)

end MathlibModel

end KIP126.Core.SpectralSequence
