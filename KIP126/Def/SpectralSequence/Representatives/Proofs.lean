import KIP126.Def.SpectralSequence.FilteredComplex.Data
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Representatives for filtered-complex differentials

This file connects the associated-graded differential of a filtered complex
with filtration-level generalized-element representatives. The representative
equations are adapted from
`KIPInfra/SpectralSequence/FilteredComplex.lean` at commit `65de864`.
Unlike that source, this module uses the project's existing filtered and
associated-graded functors and does not introduce a spectral-sequence engine.

The leading-term projection used by these representative calculations is the
existing `Algebra.Filtration.toAssociatedGraded`; no second spectral-sequence
or associated-graded interface is introduced here.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The associated-graded differential has value `b` on a generalized
element `a` exactly when `a` and `b` admit filtration-level representatives
related by the original differential. Projectivity is the categorical
replacement for choosing a lift through the leading-term epimorphism. -/
theorem FilteredComplex.associatedGradedDifferential_iff_representative
    (FC : FilteredComplex C) (s k : ℤ) {T : C} [Projective T]
    (a : T ⟶ FC.filtration.associatedGraded s k)
    (b : T ⟶ FC.filtration.associatedGraded s (k - 1)) :
    a ≫ FC.associatedGradedDifferential s k = b ↔
      ∃ x : T ⟶ Subobject.underlying.obj (FC.filtration.F s k),
        x ≫ FC.filtration.toAssociatedGraded s k = a ∧
        ∃ dx : T ⟶ Subobject.underlying.obj (FC.filtration.F s (k - 1)),
          dx ≫ (FC.filtration.F s (k - 1)).arrow =
            x ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ∧
          dx ≫ FC.filtration.toAssociatedGraded s (k - 1) = b := by
  constructor
  · intro hab
    haveI : Epi (FC.filtration.toAssociatedGraded s k) := by
      unfold Algebra.Filtration.toAssociatedGraded Algebra.Filtration.associatedGraded
      infer_instance
    let x := Projective.factorThru a (FC.filtration.toAssociatedGraded s k)
    have hx : x ≫ FC.filtration.toAssociatedGraded s k = a :=
      Projective.factorThru_comp _ _
    let dx := x ≫ (FC.differential_preserves s k).choose
    refine ⟨x, hx, dx, ?_, ?_⟩
    · rw [Category.assoc, (FC.differential_preserves s k).choose_spec]
    · calc
        dx ≫ FC.filtration.toAssociatedGraded s (k - 1) =
            x ≫ ((FC.differential_preserves s k).choose ≫
              FC.filtration.toAssociatedGraded s (k - 1)) := by
                simp only [dx, Category.assoc]
        _ = x ≫ (FC.filtration.toAssociatedGraded s k ≫
              FC.associatedGradedDifferential s k) := by
                rw [FC.toAssociatedGraded_comp_associatedGradedDifferential]
        _ = a ≫ FC.associatedGradedDifferential s k := by
                simpa only [Category.assoc] using
                  congrArg (fun q => q ≫ FC.associatedGradedDifferential s k) hx
        _ = b := hab
  · rintro ⟨x, hx, dx, hdx, hdxLead⟩
    have hdx_eq : dx = x ≫ (FC.differential_preserves s k).choose := by
      apply (cancel_mono (FC.filtration.F s (k - 1)).arrow).mp
      rw [hdx, Category.assoc, (FC.differential_preserves s k).choose_spec]
    calc
      a ≫ FC.associatedGradedDifferential s k =
          (x ≫ FC.filtration.toAssociatedGraded s k) ≫
            FC.associatedGradedDifferential s k := by rw [hx]
      _ = x ≫ ((FC.differential_preserves s k).choose ≫
          FC.filtration.toAssociatedGraded s (k - 1)) := by
            rw [Category.assoc,
              FC.toAssociatedGraded_comp_associatedGradedDifferential]
      _ = dx ≫ FC.filtration.toAssociatedGraded s (k - 1) := by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ FC.filtration.toAssociatedGraded s (k - 1))
                hdx_eq.symm
      _ = b := hdxLead

/-- An associated-graded class is a cycle exactly when it has a
filtration-level representative whose differential lifts to the next
filtration level. -/
theorem FilteredComplex.associatedGradedDifferential_eq_zero_iff_representative
    (FC : FilteredComplex C) (s k : ℤ) {T : C} [Projective T]
    (a : T ⟶ FC.filtration.associatedGraded s k) :
    a ≫ FC.associatedGradedDifferential s k = 0 ↔
      ∃ x : T ⟶ Subobject.underlying.obj (FC.filtration.F s k),
        x ≫ FC.filtration.toAssociatedGraded s k = a ∧
        ∃ dx : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + 1) (k - 1)),
          dx ≫ (FC.filtration.F (s + 1) (k - 1)).arrow =
            x ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
  constructor
  · intro ha
    obtain ⟨x, hx, dx, hdx, hdxLead⟩ :=
      (FC.associatedGradedDifferential_iff_representative s k a 0).mp ha
    obtain ⟨dx', hdx'⟩ :=
      (FC.filtration.comp_toAssociatedGraded_eq_zero_iff_lifts s (k - 1) dx).mp hdxLead
    refine ⟨x, hx, dx', ?_⟩
    calc
      dx' ≫ (FC.filtration.F (s + 1) (k - 1)).arrow =
          (dx' ≫ Subobject.ofLE (FC.filtration.F (s + 1) (k - 1))
            (FC.filtration.F s (k - 1)) (FC.filtration.decreasing s (k - 1))) ≫
            (FC.filtration.F s (k - 1)).arrow := by
              rw [Category.assoc, Subobject.ofLE_arrow]
      _ = dx ≫ (FC.filtration.F s (k - 1)).arrow := by rw [hdx']
      _ = x ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := hdx
  · rintro ⟨x, hx, dx, hdx⟩
    apply (FC.associatedGradedDifferential_iff_representative s k a 0).mpr
    let inclusion := Subobject.ofLE (FC.filtration.F (s + 1) (k - 1))
      (FC.filtration.F s (k - 1)) (FC.filtration.decreasing s (k - 1))
    refine ⟨x, hx, dx ≫ inclusion, ?_, ?_⟩
    · rw [Category.assoc, Subobject.ofLE_arrow, hdx]
    · have hinclusion :
          inclusion ≫ FC.filtration.toAssociatedGraded s (k - 1) = 0 := by
        dsimp only [inclusion, Algebra.Filtration.toAssociatedGraded]
        exact cokernel.condition _
      rw [Category.assoc, hinclusion, comp_zero]

/-- A filtered chain map carries a representative of a differential from any
source filtration level to any target filtration level. Specializing
`targetLevel = sourceLevel + r` gives the cycle lift; specializing
`sourceLevel = targetLevel - r + 1` gives the boundary lift. -/
theorem FilteredComplex.Morphism.differentialRepresentative_naturality
    {FC GD : FilteredComplex C} (f : FC ⟶ GD)
    (sourceLevel targetLevel k : ℤ) {T : C}
    (x : T ⟶ Subobject.underlying.obj (FC.filtration.F sourceLevel k))
    (dx : T ⟶ Subobject.underlying.obj
      (FC.filtration.F targetLevel (k - 1)))
    (hdx : dx ≫ (FC.filtration.F targetLevel (k - 1)).arrow =
      x ≫ (FC.filtration.F sourceLevel k).arrow ≫ FC.complex.d k (k - 1)) :
    (dx ≫ (f.preserves targetLevel (k - 1)).choose) ≫
        (GD.filtration.F targetLevel (k - 1)).arrow =
      (x ≫ (f.preserves sourceLevel k).choose) ≫
        (GD.filtration.F sourceLevel k).arrow ≫ GD.complex.d k (k - 1) := by
  calc
    (dx ≫ (f.preserves targetLevel (k - 1)).choose) ≫
          (GD.filtration.F targetLevel (k - 1)).arrow =
        dx ≫ ((f.preserves targetLevel (k - 1)).choose ≫
          (GD.filtration.F targetLevel (k - 1)).arrow) := by
      simp only [Category.assoc]
    _ = dx ≫ (FC.filtration.F targetLevel (k - 1)).arrow ≫
        f.map.f (k - 1) := by
      rw [(f.preserves targetLevel (k - 1)).choose_spec]
    _ = x ≫ (FC.filtration.F sourceLevel k).arrow ≫
        FC.complex.d k (k - 1) ≫ f.map.f (k - 1) := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ f.map.f (k - 1)) hdx
    _ = x ≫ (FC.filtration.F sourceLevel k).arrow ≫
        (f.map.f k ≫ GD.complex.d k (k - 1)) := by
      simpa only [Category.assoc] using
        congrArg (fun q => x ≫ (FC.filtration.F sourceLevel k).arrow ≫ q)
          (f.map.comm k (k - 1)).symm
    _ = x ≫ ((f.preserves sourceLevel k).choose ≫
        (GD.filtration.F sourceLevel k).arrow) ≫
          GD.complex.d k (k - 1) := by
      simpa only [Category.assoc] using
        congrArg (fun q => x ≫ q ≫ GD.complex.d k (k - 1))
          (f.preserves sourceLevel k).choose_spec.symm
    _ = (x ≫ (f.preserves sourceLevel k).choose) ≫
        (GD.filtration.F sourceLevel k).arrow ≫
          GD.complex.d k (k - 1) := by simp only [Category.assoc]

end KIP126.Core.SpectralSequence
