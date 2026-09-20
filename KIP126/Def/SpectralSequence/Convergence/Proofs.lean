import KIP126.Def.SpectralSequence.Convergence.Predicates
import KIP126.Def.Algebra.Completion.Proofs

/-! Derived completion and detection properties for strong convergence. -/
namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

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

variable {FC : FilteredComplex C} {P : EndpointExtension FC}
variable {A : Type*} [Category A] [Abelian A]
variable {F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A}
variable [F.ShiftSequence ℤ] [F.IsHomological]

/-- A supplied page/abutment comparison can be extended to coherent strong
convergence data.  The construction remains an open proof obligation for the
canonical interface. -/
theorem strongConvergenceFromComparison :
    ∀ {C : Type u} [Category.{v} C] [Abelian C]
      (FC : FilteredComplex C) (P : EndpointExtension FC)
      (A : Type u) [Category.{v} A] [Abelian A]
      (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
      [F.ShiftSequence ℤ] [F.IsHomological]
      (W : PageAbutmentComparisonWitness P A F),
      ∃ S : StrongConvergenceWitness P A F, S.comparison = W := by
  sorry

end KIP126.Core.SpectralSequence
