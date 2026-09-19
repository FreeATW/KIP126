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

/-- A generalized element of a fixed page object. -/
abbrev PageElement (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (k : κ) (T : C) := T ⟶ (E.page r hr).X k

/-- The page differential component used by a relation. -/
abbrev PageDifferential (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (source target : κ) := (E.page r hr).d source target

/-- A differential together with the filtration degree of its source. -/
structure DifferentialDatum (E : SpectralSequence C c r₀) where
  page : ℤ
  page_ge : r₀ ≤ page
  source : κ
  target : κ
  filtrationDegree : κ → ℤ

namespace DifferentialDatum

variable {E : SpectralSequence C c r₀}

abbrev sourceDegree (D : DifferentialDatum (c := c) (r₀ := r₀) E) : ℤ :=
  D.filtrationDegree D.source

end DifferentialDatum

end KIP126.Def.PageExtensions
