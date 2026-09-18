import KIP126.Def.SpectralSequence.EndpointExtension.Data
import KIP126.Def.Algebra.Completion.Proofs

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

namespace PageAbutmentComparisonWitness

variable {FC : FilteredComplex C} {P : EndpointExtension FC}
variable {A : Type*} [Category A] [Abelian A]
variable {F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A}
variable [F.ShiftSequence ℤ] [F.IsHomological]

/-- The bounded-above component of the regularity data supplies the canonical
degreewise completion witness. -/
noncomputable def completion (W : PageAbutmentComparisonWitness P A F) (n : ℤ) :
    Algebra.Filtration.CompletionWitness W.filtration n :=
  Algebra.Filtration.CompletionWitness.of_isBoundedAbove W.filtration
    W.bounded.toIsBoundedAbove n

/-- The bounded-below part of the witness makes the abutment filtration
degreewise eventually top (the project predicate named `IsExhaustive`). -/
lemma exhaustive (W : PageAbutmentComparisonWitness P A F) :
    W.filtration.IsExhaustive :=
  W.bounded.toIsBoundedBelow.isExhaustive

/-- The bounded-above part of the witness makes the abutment filtration
degreewise eventually bottom, which is stronger than separatedness. -/
lemma eventuallyZero (W : PageAbutmentComparisonWitness P A F) :
    W.filtration.IsEventuallyZero :=
  W.bounded.toIsBoundedAbove.isEventuallyZero

end PageAbutmentComparisonWitness

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

namespace StrongConvergenceWitness

variable {FC : FilteredComplex C} {P : EndpointExtension FC}
variable {A : Type*} [Category A] [Abelian A]
variable {F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A}
variable [F.ShiftSequence ℤ] [F.IsHomological]

/-- The comparison from any stable page to the associated graded, factored
through the coherent limiting page. -/
noncomputable def pageComparison (W : StrongConvergenceWitness P A F)
    (pq : ℤ × ℤ) (r : ℤ) (hr : W.comparison.comparisonPage pq ≤ r) :
    ((P.spectralSequence A F).page r
      ((W.comparison.comparisonPage_ge_two pq).trans hr)).X pq ≅
        W.comparison.filtration.associatedGraded
          (W.comparison.filtrationDegree pq) (pq.1 + pq.2) :=
  (W.pageIso pq r hr).trans (W.eInfinityComparison pq)

/-- The stable-page comparisons with the associated graded commute with
Mathlib's successor-page isomorphisms. -/
@[simp]
lemma pagePassage_pageComparison (W : StrongConvergenceWitness P A F)
    (pq : ℤ × ℤ) (r : ℤ) (hr : W.comparison.comparisonPage pq ≤ r) :
    (W.pageHomologyIso pq r hr).inv ≫
        ((P.spectralSequence A F).iso r (r + 1) pq rfl
          ((W.comparison.comparisonPage_ge_two pq).trans hr)).hom ≫
      (W.pageComparison pq (r + 1) (hr.trans (by omega))).hom =
        (W.pageComparison pq r hr).hom := by
  simp only [pageComparison, Iso.trans_hom]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ (W.eInfinityComparison pq).hom)
    (W.pagePassage_coherent pq r hr)

/-- The coherent stable-page comparison restricts to the selected pointwise
comparison stored by the underlying witness. -/
@[simp]
lemma pageComparison_selected (W : StrongConvergenceWitness P A F)
    (pq : ℤ × ℤ) :
    W.pageComparison pq (W.comparison.comparisonPage pq) le_rfl =
      W.comparison.pageComparison pq := by
  apply Iso.ext
  exact W.selectedPage_compat pq

/-- A limiting class detects a filtered generalized element when their images
agree in the associated graded piece selected by the bidegree.  Detection is
a relation: changing the filtered lift by the next filtration level does not
change the detected limiting class. -/
def Detects (W : StrongConvergenceWitness P A F)
    {T : A} {pq : ℤ × ℤ}
    (y : T ⟶ W.eInfinity pq)
    (x : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) : Prop :=
  y ≫ (W.eInfinityComparison pq).hom =
    x ≫ W.comparison.filtration.toAssociatedGraded
      (W.comparison.filtrationDegree pq) (pq.1 + pq.2)

/-- The zero limiting class detects exactly the generalized elements that
lift to the next filtration level. -/
theorem detect_zero (W : StrongConvergenceWitness P A F)
    {T : A} {pq : ℤ × ℤ}
    (x : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) :
    W.Detects (0 : T ⟶ W.eInfinity pq) x ↔
      ∃ x' : T ⟶ Subobject.underlying.obj
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2)),
        x' ≫ Subobject.ofLE
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2))
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq) (pq.1 + pq.2))
          (W.comparison.filtration.decreasing
            (W.comparison.filtrationDegree pq) (pq.1 + pq.2)) = x := by
  simpa only [Detects, Limits.zero_comp, eq_comm] using
    W.comparison.filtration.comp_toAssociatedGraded_eq_zero_iff_lifts
      (W.comparison.filtrationDegree pq) (pq.1 + pq.2) x

/-- The conjunction that `y` detects both filtered generalized elements is
equivalent to `y` detecting `x` and the difference `x - x'` lifting through
the next filtration level.  Thus, assuming `y` detects `x`, it also detects
`x'` exactly when that difference lifts. -/
theorem detect_difference (W : StrongConvergenceWitness P A F)
    {T : A} {pq : ℤ × ℤ}
    (y : T ⟶ W.eInfinity pq)
    (x x' : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) :
    (W.Detects y x ∧ W.Detects y x') ↔
      (W.Detects y x ∧
        ∃ z : T ⟶ Subobject.underlying.obj
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2)),
          z ≫ Subobject.ofLE
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2))
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq) (pq.1 + pq.2))
            (W.comparison.filtration.decreasing
              (W.comparison.filtrationDegree pq) (pq.1 + pq.2)) = x - x') := by
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, (W.comparison.filtration.comp_toAssociatedGraded_eq_iff_sub_lifts
      (W.comparison.filtrationDegree pq) (pq.1 + pq.2) x x').mp ?_⟩
    rw [Detects] at hx hx'
    exact hx.symm.trans hx'
  · rintro ⟨hx, hlift⟩
    refine ⟨hx, ?_⟩
    rw [Detects] at hx ⊢
    exact hx.trans
      ((W.comparison.filtration.comp_toAssociatedGraded_eq_iff_sub_lifts
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2) x x').mpr hlift)

end StrongConvergenceWitness

end KIP126.Core.SpectralSequence
