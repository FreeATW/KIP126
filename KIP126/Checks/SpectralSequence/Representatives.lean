import KIP126.Def.SpectralSequence.Representatives.Proofs

/-!
# Regression checks for filtered representatives

These examples keep the representative bridge connected to filtered-complex
morphisms and the associated-graded functor.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

section FilteredRepresentatives

variable (FC : FilteredComplex C) (s k : ℤ) {T : C} [Projective T]

example (a : T ⟶ FC.filtration.associatedGraded s k)
    (b : T ⟶ FC.filtration.associatedGraded s (k - 1)) :
    a ≫ FC.associatedGradedDifferential s k = b ↔
      ∃ x : T ⟶ Subobject.underlying.obj (FC.filtration.F s k),
        x ≫ FC.filtration.toAssociatedGraded s k = a ∧
        ∃ dx : T ⟶ Subobject.underlying.obj (FC.filtration.F s (k - 1)),
          dx ≫ (FC.filtration.F s (k - 1)).arrow =
            x ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ∧
          dx ≫ FC.filtration.toAssociatedGraded s (k - 1) = b :=
  FC.associatedGradedDifferential_iff_representative s k a b

example (a : T ⟶ FC.filtration.associatedGraded s k) :
    a ≫ FC.associatedGradedDifferential s k = 0 ↔
      ∃ x : T ⟶ Subobject.underlying.obj (FC.filtration.F s k),
        x ≫ FC.filtration.toAssociatedGraded s k = a ∧
        ∃ dx : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + 1) (k - 1)),
          dx ≫ (FC.filtration.F (s + 1) (k - 1)).arrow =
            x ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) :=
  FC.associatedGradedDifferential_eq_zero_iff_representative s k a

end FilteredRepresentatives

example {FC GD : FilteredComplex C} (f : FC ⟶ GD)
    (s k : ℤ) (page : ℕ) {T : C}
    (x : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
    (dx : T ⟶ Subobject.underlying.obj
      (FC.filtration.F (s + page) (k - 1)))
    (hdx : dx ≫ (FC.filtration.F (s + page) (k - 1)).arrow =
      x ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) :
    (dx ≫ (f.preserves (s + page) (k - 1)).choose) ≫
        (GD.filtration.F (s + page) (k - 1)).arrow =
      (x ≫ (f.preserves s k).choose) ≫
        (GD.filtration.F s k).arrow ≫ GD.complex.d k (k - 1) :=
  f.differentialRepresentative_naturality s (s + page) k x dx hdx

example {FC GD : FilteredComplex C} (f : FC ⟶ GD)
    (s k : ℤ) (page : ℕ) {T : C}
    (y : T ⟶ Subobject.underlying.obj
      (FC.filtration.F (s - page + 1) k))
    (dy : T ⟶ Subobject.underlying.obj (FC.filtration.F s (k - 1)))
    (hdy : dy ≫ (FC.filtration.F s (k - 1)).arrow =
      y ≫ (FC.filtration.F (s - page + 1) k).arrow ≫
        FC.complex.d k (k - 1)) :
    (dy ≫ (f.preserves s (k - 1)).choose) ≫
        (GD.filtration.F s (k - 1)).arrow =
      (y ≫ (f.preserves (s - page + 1) k).choose) ≫
        (GD.filtration.F (s - page + 1) k).arrow ≫
          GD.complex.d k (k - 1) :=
  f.differentialRepresentative_naturality (s - page + 1) s k y dy hdy

example {FC GD : FilteredComplex C} (f : FC ⟶ GD) (s k : ℤ) :
    FC.filtration.toAssociatedGraded s k ≫ f.associatedGradedMap s k =
      (f.preserves s k).choose ≫ GD.filtration.toAssociatedGraded s k :=
  Algebra.FilteredMorphism.toAssociatedGraded_comp_associatedGradedMap
    f.toFilteredMorphism s k

end

end KIP126.Core.SpectralSequence
