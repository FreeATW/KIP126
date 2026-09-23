import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Mathlib spectral-sequence foundation

The shared spectral-sequence object is
`CategoryTheory.SpectralSequence`.  This module is deliberately an import
boundary only: KIP126 does not introduce an alias, wrapper, or competing
`SpectralSequence` structure here.

Project-specific constructions belong in their own modules only when a
downstream use requires mathematics absent from Mathlib.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

/-! The following examples are compile-time API regression checks, not a
second project interface. -/

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- A Mathlib spectral sequence exposes its page at every admissible page
index. -/
example (E : CategoryTheory.SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) :
    HomologicalComplex C (c r) :=
  E.page r hr

/-- The differential of an exposed page is the differential of its
homological complex. -/
example (E : CategoryTheory.SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (p q : κ) :
    (E.page r hr).X p ⟶ (E.page r hr).X q :=
  (E.page r hr).d p q

/-- Mathlib supplies the page-passage isomorphism from page homology to the
next page. -/
example (E : CategoryTheory.SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (p : κ) :
    (E.page r hr).homology p ≅ (E.page (r + 1) (by omega)).X p :=
  E.iso r (r + 1) p rfl hr

end KIP126.Core.SpectralSequence
