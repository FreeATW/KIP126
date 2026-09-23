import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
import KIP126.Def.SpectralSequence.Convergence.SSData.Predicates

/-!
# Boundedness of the filtered two-term complex
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_fil_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    (underlyingComplex aMap hcompat t).fil s 1 = F₁.F s t := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_fil_zero
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    (underlyingComplex aMap hcompat t).fil s 0 = F₂.F s t := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_d_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') :
    (underlyingComplex aMap hcompat t).d 1 = aMap t := by
  change (BoundedExtension.twoTermComplex (A₁ t) (A₂ t) (aMap t)).d 1 0 = aMap t
  exact BoundedExtension.twoTermComplex_d_one (A₁ t) (A₂ t) (aMap t)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_filDiff_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    (underlyingComplex aMap hcompat t).filDiff s 1 =
      (hcompat s t).choose := by
  apply (cancel_mono (F₂.F s t).arrow).mp
  calc
    (underlyingComplex aMap hcompat t).filDiff s 1 ≫ (F₂.F s t).arrow =
        (F₁.F s t).arrow ≫ aMap t :=
      by
        simpa [FilteredComplex.filDiff, FilteredComplex.fil, FilteredComplex.d,
          underlyingComplex, twoTermFil, BoundedExtension.twoTermFil,
          BoundedExtension.twoTermComplex_d_one] using
          (underlyingComplex aMap hcompat t).differential_preserves s 1 |>.choose_spec
    _ = (hcompat s t).choose ≫ (F₂.F s t).arrow :=
      (hcompat s t).choose_spec.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_filToAssocGraded_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    (underlyingComplex aMap hcompat t).filToAssocGraded s 1 =
      F₁.toAssociatedGraded s t := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem underlyingComplex_filToAssocGraded_zero
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    (underlyingComplex aMap hcompat t).filToAssocGraded s 0 =
      F₂.toAssociatedGraded s t := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the page-zero differential with the filtration quotient
maps, specialized to the nonzero differential of the two-term complex. -/
theorem underlyingComplex_assocGradedDiff_compat_one
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (s : ℤ) :
    F₁.toAssociatedGraded s t ≫
        (underlyingComplex aMap hcompat t).assocGradedDiff s 1 =
      (hcompat s t).choose ≫ F₂.toAssociatedGraded s t := by
  rw [← underlyingComplex_filToAssocGraded_one aMap hcompat t s]
  rw [FilteredComplex.assocGradedDiff_compat]
  change (underlyingComplex aMap hcompat t).filDiff s 1 ≫
      (underlyingComplex aMap hcompat t).filToAssocGraded s 0 =
    (hcompat s t).choose ≫ F₂.toAssociatedGraded s t
  simp only [underlyingComplex_filDiff_one,
    underlyingComplex_filToAssocGraded_zero]

private lemma subobject_eq_bot_of_isZero {X : C} (hX : IsZero X)
    (P : Subobject X) : P = ⊥ := by
  have hP_zero : IsZero (Subobject.underlying.obj P) := hX.of_mono P.arrow
  apply le_antisymm
  · apply Subobject.le_of_comm (hP_zero.to_ _)
    apply hX.eq_of_tgt
  · exact bot_le

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Bounded target filtrations induce a bounded filtration on the two-term complex. -/
noncomputable def underlyingComplexBounded
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) :
    (underlyingComplex aMap hcompat t).IsBounded where
  lo := fun k => if k = 1 then bnd₁.lo t else if k = 0 then bnd₂.lo t else 0
  hi := fun k => if k = 1 then bnd₁.hi t else if k = 0 then bnd₂.hi t else 0
  lo_le_hi := fun k => by
    by_cases h₁ : k = 1
    · simp only [h₁, ↓reduceIte]
      exact bnd₁.lo_le_hi t
    · by_cases h₀ : k = 0
      · simp only [h₀, ↓reduceIte]
        exact bnd₂.lo_le_hi t
      · simp [h₁, h₀]
  boundedBelow := fun k s hs => by
    simp only [FilteredComplex.fil]
    unfold underlyingComplex
    by_cases h₁ : k = 1
    · subst k
      simpa [twoTermFil, BoundedExtension.twoTermFil] using
        bnd₁.boundedBelow t s hs
    · by_cases h₀ : k = 0
      · subst k
        simpa [twoTermFil, BoundedExtension.twoTermFil] using
          bnd₂.boundedBelow t s hs
      · simp [twoTermFil, BoundedExtension.twoTermFil, h₁, h₀]
  boundedAbove := fun k s hs => by
    simp only [FilteredComplex.fil]
    unfold underlyingComplex
    by_cases h₁ : k = 1
    · subst k
      simpa [twoTermFil, BoundedExtension.twoTermFil] using
        bnd₁.boundedAbove t s hs
    · by_cases h₀ : k = 0
      · subst k
        simpa [twoTermFil, BoundedExtension.twoTermFil] using
          bnd₂.boundedAbove t s hs
      · simp only [if_neg h₁, if_neg h₀] at hs
        have hz : IsZero
            ((BoundedExtension.twoTermComplex (A₁ t) (A₂ t) (aMap t)).X k) := by
          rw [BoundedExtension.twoTermComplex_X]
          rw [BoundedExtension.twoTermObj_other (A₁ t) (A₂ t) k h₁ h₀]
          exact IsInitial.isZero initialIsInitial
        simp [twoTermFil, BoundedExtension.twoTermFil, h₁, h₀]
        exact subobject_eq_bot_of_isZero hz ⊤

end KIP126.Core.SpectralSequence
