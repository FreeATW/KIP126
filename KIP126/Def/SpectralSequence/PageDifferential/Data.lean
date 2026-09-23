import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Page-level differential data

This file defines the generic data used to state differential equations on a
page of a Mathlib spectral sequence.  It is independent of filtered-complex
representatives and of the paper-specific `(f, E_r)` page-extension theory.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} (c : ℤ → ComplexShape κ) (r₀ : ℤ)

namespace MathlibModel

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

end MathlibModel

end KIP126.Core.SpectralSequence
