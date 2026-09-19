import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Page-level differential relations

The historical KIPBase crossing API used the nested `Z/B` presentation of a
spectral sequence.  KIP126 uses Mathlib's page kernel instead: a page element
is a generalized element of a page object, and a differential relation is the
single page equation obtained by composing with the page differential.  This
file owns only that data-level interface; filtration and crossing predicates
are in `Predicates.lean`.
-/

namespace KIP126.Def.PageExtensions

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} (c : ℤ → ComplexShape κ) (r₀ : ℤ)

abbrev SpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (c : ℤ → ComplexShape κ) (r₀ : ℤ) :=
  CategoryTheory.SpectralSequence C c r₀

/-- A generalized element of a fixed page object. -/
abbrev PageElement (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (k : κ) (T : C) := T ⟶ (E.page r hr).X k

/-- The page differential component used by a relation. -/
abbrev PageDifferential (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (source target : κ) := (E.page r hr).d source target

/-- A differential at `(r, source, target)` is essential when its page map is
nonzero.  The `target` is explicit because Mathlib's complex shape may admit
more than one target index in a general page interface. -/
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

/-- An essential relation packages the relation and the fact that the page map
itself is nonzero. -/
def EssentialDifferentialRelation (E : SpectralSequence C c r₀) (r : ℤ)
    (hr : r₀ ≤ r) (source target : κ) {T : C}
    (x : PageElement c r₀ E r hr source T)
    (y : PageElement c r₀ E r hr target T) : Prop :=
  DifferentialRelation c r₀ E r hr source target x y ∧
    IsEssentialAt c r₀ E r hr source target

end KIP126.Def.PageExtensions
