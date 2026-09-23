import KIP126.Def.Algebra.Filtration.Proofs
import KIP126.Def.SpectralSequence.FilteredComplex.Data
import KIP126.Def.SpectralSequence.FilteredPage.Data
import KIP126.Def.SpectralSequence.FilteredPage.AssemblyProofs
import KIP126.Def.SpectralSequence.PageDifferential.Proofs

/-!
# Data for filtered-complex/page relations

This file contains only the objects used to compare filtered-complex lifts
with page elements.  Their properties live in `Predicates.lean`, and the
mathematical relation lemmas live in `Proofs.lean`.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A page-level view of the canonical quotient pages of a filtered complex.

The comparison with Mathlib's page objects is explicit data.  In particular,
this structure does not silently identify a page with the associated graded
object.
-/
structure PageView (FC : FilteredComplex C) where
  shape : ℤ → ComplexShape (ℤ × ℤ)
  firstPage : ℤ
  sequence : CategoryTheory.SpectralSequence C shape firstPage
  /-- Translate Mathlib's integer page index to the canonical finite/infinite
  page index. -/
  pageNumber : ∀ (r : ℤ), firstPage ≤ r → WithTop ℕ
  /-- Comparison with the quotient page built from canonical cycles and
  boundaries. -/
  pageToPage : ∀ (r : ℤ) (hr : firstPage ≤ r) (s k : ℤ),
    (sequence.page r hr).X (s, k) ≅
      FC.pageObj s k (pageNumber r hr)

/-- The canonical page view of a filtered complex. -/
noncomputable def PageView.canonical
    (FC : FilteredComplex C) : PageView FC where
  shape := fun r : ℤ => pageShape r.toNat
  firstPage := 0
  sequence := FC.canonicalPageSpectralSequence
  pageNumber := fun r _ => (r.toNat : WithTop ℕ)
  pageToPage := fun _ _ _ _ => Iso.refl _

namespace PageView

variable {FC : FilteredComplex C} (P : PageView FC)

abbrev element (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ) (T : C) :=
  T ⟶ (P.sequence.page r hr).X (s, k)

def target (r s k : ℤ) : ℤ × ℤ := (s + r, k - 1)

/-- The canonical filtration differential supplied by `FilteredComplex`. -/
noncomputable def filDiff (s k : ℤ) :
    Subobject.underlying.obj (FC.filtration.F s k) ⟶
      Subobject.underlying.obj (FC.filtration.F s (k - 1)) :=
  (FC.differential_preserves s k).choose

/-- The canonical inclusion from `F^(s+r)` to `F^s`, when `r ≥ 0`. -/
noncomputable def drop (r s k : ℤ) (hr : 0 ≤ r) :
    Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1)) ⟶
      Subobject.underlying.obj (FC.filtration.F s (k - 1)) :=
  FC.filtration.inclusion (by omega) (k - 1)

def datum (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ) :
    MathlibModel.DifferentialDatum (c := P.shape) (r₀ := P.firstPage) P.sequence where
  page := r
  page_ge := hr
  source := (s, k)
  target := target r s k
  filtrationDegree := fun p => p.1

end PageView

end KIP126.Core.SpectralSequence.FilteredComplex
