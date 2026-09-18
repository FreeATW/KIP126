import KIP126.Def.SpectralSequence.EndpointExtension.Data
import KIP126.Def.Algebra.Completion.Data

/-! Convergence and detection witnesses for an endpoint-extended spectral sequence. -/
namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Explicit input for comparing pointwise selected pages of an endpoint-extended
spectral sequence with the associated graded of a complete, degreewise bounded
endpoint abutment filtration.  The record is deliberately narrower than a
strong convergence theorem: it stores one selected page for each bidegree, but
does not claim the additional page-passage coherence needed to construct a
canonical `E∞` object.

Completeness is proved from the canonical tower `Aᵢ / FˢAᵢ`, while the
boundedness field proves degreewise eventual-top and eventual-bottom
consequences.  These are stronger than ordinary exhaustiveness and
separatedness.
All of this remains explicit data for a concrete construction; it is not
inferred from an arbitrary filtered complex. -/
structure PageAbutmentComparisonWitness
    {FC : FilteredComplex C} (P : EndpointExtension FC) (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] where
  /-- The endpoint limit/colimit data for the diagram that produced the
spectral sequence. -/
  boundary : P.BoundaryWitness
  /-- The chosen graded abutment. -/
  abutment : CategoryTheory.GradedObject ℤ A
  /-- The chosen abutment is explicitly the shifted homological image of the
upper endpoint.  This keeps the associated-graded comparison connected to the
same endpoint data that supplied the boundary witnesses. -/
  endpointAbutmentIso : P.endpointAbutment A F ≅ abutment
  /-- Its decreasing filtration.  This is separate data because the filtration
on an abutment need not be definitionally the filtration on a chain complex. -/
  filtration : Algebra.Filtration abutment
  /-- Degreewise boundedness is the regularity hypothesis used here.  Its lower
and upper components imply degreewise eventual-top, eventual-bottom, and
canonical degreewise completion respectively. -/
  bounded : Algebra.Filtration.IsBounded filtration
  /-- Which abutment-filtration degree represents a page bidegree.  Keeping
this translation explicit prevents a hidden sign or page-index convention. -/
  filtrationDegree : ℤ × ℤ → ℤ
  /-- The page selected by the concrete comparison at each bidegree.  It is
intentionally bidegree-dependent; no uniform-page or page-passage coherence is
claimed by this witness. -/
  comparisonPage : ℤ × ℤ → ℤ
  comparisonPage_ge_two : ∀ pq, 2 ≤ comparisonPage pq
  /-- Each pointwise selected page is explicitly identified with the associated
graded piece of the chosen endpoint abutment. -/
  pageComparison : ∀ pq,
    ((P.spectralSequence A F).page (comparisonPage pq)
      (comparisonPage_ge_two pq)).X pq ≅
        filtration.associatedGraded (filtrationDegree pq) (pq.1 + pq.2)

/-- Coherent strong-convergence data built on a pointwise page/abutment
comparison.  Mathlib deliberately has no distinguished `E∞` page, so the
limiting page is explicit data.  Every sufficiently late page is identified
with that object, the identifications commute with Mathlib's successor-page
isomorphisms, and the limiting page is identified with the associated graded
of the endpoint abutment filtration.

This interface adapts the convergence and detection proof pattern from
`KIP/SpectralSequence/Convergence.lean` at commit
`19a6a56c6c1e590dde850f33a18490b8f35e7d6e` to Mathlib's spectral-sequence
kernel and KIP126's explicit endpoint witnesses. -/
structure StrongConvergenceWitness
    {FC : FilteredComplex C} (P : EndpointExtension FC)
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] where
  /-- The selected-page comparison and bounded endpoint data on which strong
  convergence is built. -/
  comparison : PageAbutmentComparisonWitness P A F
  /-- The coherent limiting page, indexed by spectral-sequence bidegree. -/
  eInfinity : CategoryTheory.GradedObject (ℤ × ℤ) A
  /-- Supplied identifications from stable-page homology to the stable-page
  object at the selected bidegree. -/
  pageHomologyIso : ∀ (pq : ℤ × ℤ) (r : ℤ)
      (hr : comparison.comparisonPage pq ≤ r),
    ((P.spectralSequence A F).page r
      ((comparison.comparisonPage_ge_two pq).trans hr)).homology pq ≅
        ((P.spectralSequence A F).page r
          ((comparison.comparisonPage_ge_two pq).trans hr)).X pq
  /-- Every page after the selected stable bound is identified with `E∞`. -/
  pageIso : ∀ (pq : ℤ × ℤ) (r : ℤ)
      (hr : comparison.comparisonPage pq ≤ r),
    ((P.spectralSequence A F).page r
      ((comparison.comparisonPage_ge_two pq).trans hr)).X pq ≅ eInfinity pq
  /-- The stable-page identifications commute with Mathlib's page passage. -/
  pagePassage_coherent : ∀ (pq : ℤ × ℤ) (r : ℤ)
      (hr : comparison.comparisonPage pq ≤ r),
    (pageHomologyIso pq r hr).inv ≫
        ((P.spectralSequence A F).iso r (r + 1) pq rfl
          ((comparison.comparisonPage_ge_two pq).trans hr)).hom ≫
      (pageIso pq (r + 1) (hr.trans (by omega))).hom =
        (pageIso pq r hr).hom
  /-- The limiting page is the associated graded of the chosen endpoint
  abutment filtration. -/
  eInfinityComparison : ∀ pq,
    eInfinity pq ≅ comparison.filtration.associatedGraded
      (comparison.filtrationDegree pq) (pq.1 + pq.2)
  /-- At the selected page, the coherent comparison recovers the original
  pointwise comparison. -/
  selectedPage_compat : ∀ pq,
    (pageIso pq (comparison.comparisonPage pq) le_rfl).hom ≫
        (eInfinityComparison pq).hom =
      (comparison.pageComparison pq).hom

end KIP126.Core.SpectralSequence
