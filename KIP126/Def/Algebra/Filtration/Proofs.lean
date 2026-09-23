import KIP126.Def.Algebra.Filtration.Predicates

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

namespace Filtration

variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

private lemma imageSubobject_ofLE_eq_bot_of_eq_bot [Abelian C]
    {B : C} (X Y : Subobject B) (h : X ≤ Y) (hX : X = ⊥) :
    imageSubobject (Subobject.ofLE X Y h) = ⊥ := by
  subst hX
  have hzero : Subobject.ofLE ⊥ Y h = 0 := by
    rw [← cancel_mono Y.arrow, Subobject.ofLE_arrow, Subobject.bot_arrow, zero_comp]
  rw [hzero, imageSubobject_zero]

/-- A bounded-above filtration satisfies the canonical Mittag-Leffler
condition, because all sufficiently deep images are zero. -/
lemma IsBoundedAbove.isMittagLeffler [Abelian C]
    {F : Filtration A} (hF : IsBoundedAbove F) :
    IsMittagLeffler F := by
  intro i s
  refine ⟨(hF.upper i - s).toNat, ?_⟩
  intro n hn
  have hN : hF.upper i ≤ s + ((hF.upper i - s).toNat : ℤ) := by omega
  have hn' : hF.upper i ≤ s + (n : ℤ) := by omega
  have hs_n : s ≤ s + (n : ℤ) := by omega
  have hs_N : s ≤ s + ((hF.upper i - s).toNat : ℤ) := by omega
  change imageSubobject
      (Subobject.ofLE (F.F (s + (n : ℤ)) i) (F.F s i)
        (F.le_of_le hs_n i)) =
    imageSubobject
      (Subobject.ofLE (F.F (s + ((hF.upper i - s).toNat : ℤ)) i)
        (F.F s i) (F.le_of_le hs_N i))
  rw [imageSubobject_ofLE_eq_bot_of_eq_bot _ _ (F.le_of_le hs_n i)
      (hF.eq_bot_of_le i _ hn'),
    imageSubobject_ofLE_eq_bot_of_eq_bot _ _ (F.le_of_le hs_N i)
      (hF.eq_bot_of_le i _ hN)]

lemma IsBounded.isMittagLeffler [Abelian C]
    {F : Filtration A} (hF : IsBounded F) :
    IsMittagLeffler F :=
  hF.toIsBoundedAbove.isMittagLeffler

@[simp]
lemma transportGraded_self [Abelian C] (F : Filtration A)
    {r : ℤ × ι} (h : r = r) :
    F.transportGraded h = 𝟙 (F.associatedGraded r.1 r.2) :=
  rfl

lemma transportGraded_trans [Abelian C] (F : Filtration A)
    {r₁ r₂ r₃ : ℤ × ι} (h₁₂ : r₁ = r₂) (h₂₃ : r₂ = r₃) :
    F.transportGraded h₁₂ ≫ F.transportGraded h₂₃ =
      F.transportGraded (h₁₂.trans h₂₃) := by
  subst h₁₂
  subst h₂₃
  simp only [Filtration.transportGraded_self, Category.id_comp]

/-- A generalized element of one filtration level maps to zero in the
associated graded exactly when it lifts through the next filtration level. -/
lemma comp_toAssociatedGraded_eq_zero_iff_lifts [Abelian C]
    (F : Filtration A) {T : C} (s : ℤ) (i : ι)
    (x : T ⟶ Subobject.underlying.obj (F.F s i)) :
    x ≫ F.toAssociatedGraded s i = 0 ↔
      ∃ x' : T ⟶ Subobject.underlying.obj (F.F (s + 1) i),
        x' ≫ Subobject.ofLE (F.F (s + 1) i) (F.F s i)
          (F.decreasing s i) = x := by
  unfold toAssociatedGraded associatedGraded
  constructor
  · intro h
    exact ⟨Abelian.monoLift _ x h, Abelian.monoLift_comp _ x h⟩
  · rintro ⟨x', rfl⟩
    rw [Category.assoc, cokernel.condition, Limits.comp_zero]

/-- Two generalized elements have the same associated-graded image exactly
when their difference lifts through the next filtration level. -/
lemma comp_toAssociatedGraded_eq_iff_sub_lifts [Abelian C]
    (F : Filtration A) {T : C} (s : ℤ) (i : ι)
    (x x' : T ⟶ Subobject.underlying.obj (F.F s i)) :
    x ≫ F.toAssociatedGraded s i = x' ≫ F.toAssociatedGraded s i ↔
      ∃ z : T ⟶ Subobject.underlying.obj (F.F (s + 1) i),
        z ≫ Subobject.ofLE (F.F (s + 1) i) (F.F s i)
          (F.decreasing s i) = x - x' := by
  rw [← sub_eq_zero, ← Preadditive.sub_comp]
  exact F.comp_toAssociatedGraded_eq_zero_iff_lifts s i (x - x')

/-- A bounded-below filtration is exhaustive. -/
lemma IsBoundedBelow.isExhaustive {F : Filtration A} (hF : IsBoundedBelow F) :
    IsExhaustive F := by
  intro i
  exact ⟨hF.lower i, hF.eq_top_of_le i (hF.lower i) le_rfl⟩

/-- A bounded-above filtration is eventually zero. -/
lemma IsBoundedAbove.isEventuallyZero [Abelian C] {F : Filtration A} (hF : IsBoundedAbove F) :
    IsEventuallyZero F := by
  intro i
  exact ⟨hF.upper i, hF.eq_bot_of_le i (hF.upper i) le_rfl⟩

end Filtration

namespace FilteredMorphism

variable {ι : Type w}
  {A B D : CategoryTheory.GradedObject ι C}
  {F : Filtration A} {G : Filtration B} {H : Filtration D}

/-- The quotient projections commute with the map induced on associated graded
pieces.  This is the universal-property equation used by later filtered
complex constructions. -/
lemma toAssociatedGraded_comp_associatedGradedMap [Abelian C]
    (f : FilteredMorphism F G) (s : ℤ) (i : ι) :
    F.toAssociatedGraded s i ≫ f.associatedGradedMap s i =
      (f.preserves s i).choose ≫ G.toAssociatedGraded s i := by
  unfold Filtration.toAssociatedGraded FilteredMorphism.associatedGradedMap
  dsimp only [cokernel.map]
  exact cokernel.π_desc _ _ _

@[simp]
lemma associatedGradedMap_id [Abelian C] (F : Filtration A) (s : ℤ) (i : ι) :
    (FilteredMorphism.id F).associatedGradedMap s i = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE (F.F (s + 1) i)
    (F.F s i) (F.decreasing s i)))).mp
  have h := toAssociatedGraded_comp_associatedGradedMap
    (FilteredMorphism.id F) s i
  have hi := id_preserves_eq F s i
  change F.toAssociatedGraded s i ≫
      (FilteredMorphism.id F).associatedGradedMap s i =
    F.toAssociatedGraded s i ≫ 𝟙 _
  rw [h, hi]
  simp

@[simp]
lemma associatedGradedMap_comp [Abelian C]
    (f : FilteredMorphism F G) (g : FilteredMorphism G H) (s : ℤ) (i : ι) :
    (FilteredMorphism.comp f g).associatedGradedMap s i =
      f.associatedGradedMap s i ≫ g.associatedGradedMap s i := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE (F.F (s + 1) i)
    (F.F s i) (F.decreasing s i)))).mp
  calc
    F.toAssociatedGraded s i ≫
          (FilteredMorphism.comp f g).associatedGradedMap s i =
        ((FilteredMorphism.comp f g).preserves s i).choose ≫
          H.toAssociatedGraded s i :=
      toAssociatedGraded_comp_associatedGradedMap _ _ _
    _ = (f.preserves s i).choose ≫ (g.preserves s i).choose ≫
          H.toAssociatedGraded s i := by
      rw [comp_preserves_eq]
      simp only [Category.assoc]
    _ = (f.preserves s i).choose ≫
          (G.toAssociatedGraded s i ≫ g.associatedGradedMap s i) := by
      simpa only [Category.assoc] using
        congrArg (fun q => (f.preserves s i).choose ≫ q)
          (toAssociatedGraded_comp_associatedGradedMap g s i).symm
    _ = (F.toAssociatedGraded s i ≫ f.associatedGradedMap s i) ≫
          g.associatedGradedMap s i := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ g.associatedGradedMap s i)
          (toAssociatedGraded_comp_associatedGradedMap f s i).symm
    _ = F.toAssociatedGraded s i ≫
          (f.associatedGradedMap s i ≫ g.associatedGradedMap s i) := by
      simp only [Category.assoc]

end FilteredMorphism

end KIP126.Core.Algebra
