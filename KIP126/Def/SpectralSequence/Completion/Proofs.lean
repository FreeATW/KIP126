import KIP126.Def.SpectralSequence.Completion.Predicates

/-!
# Basic completion proofs

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

/-! ### Completion of filtered objects -/

noncomputable instance Filtration.hasLimitCompletionFunctor {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) :
    HasLimit (fil.completionFunctor hbb k) := inferInstance

lemma Filtration.completionProj'_factor {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s : ℤ) :
    fil.completionProj' hbb k (s + 1) ≫ fil.truncationTransition (show s ≤ s + 1 by omega) k =
    fil.completionProj' hbb k s := by
  simp only [Filtration.completionProj', Filtration.completion,
    Filtration.completionFunctor]
  rw [Category.assoc, fil.truncationTransition_comp]
  have hw := limit.w (fil.completionFunctor hbb k)
    (homOfLE (show (s - hbb.lo k).toNat ≤ (s + 1 - hbb.lo k).toNat by omega)).op
  erw [← hw, Category.assoc, fil.truncationTransition_comp]
  all_goals simp only [Opposite.unop_op]
  · rfl
  · omega

private lemma imageSubobject_ofLE_eq_bot_of_eq_bot {B : C} (X Y : Subobject B) (h : X ≤ Y)
    (hX : X = ⊥) : imageSubobject (Subobject.ofLE X Y h) = ⊥ := by
  subst hX
  have : Subobject.ofLE ⊥ Y h = 0 := by
    rw [← cancel_mono Y.arrow, Subobject.ofLE_arrow, Subobject.bot_arrow, zero_comp]
  rw [this, imageSubobject_zero]

/-! ### Mittag-Leffler condition -/

/-- Bounded-above filtrations satisfy Mittag-Leffler. -/
theorem Filtration.IsBoundedAbove.toIsMittagLeffler {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hba : fil.IsBoundedAbove) : fil.IsMittagLeffler := by
  intro k s
  use (hba.hi k - s).toNat
  intro n hn
  have hN : hba.hi k ≤ s + ↑((hba.hi k - s).toNat) := by omega
  have hn' : hba.hi k ≤ s + ↑n := by omega
  rw [imageSubobject_ofLE_eq_bot_of_eq_bot _ _ _ (hba.boundedAbove k _ hn'),
      imageSubobject_ofLE_eq_bot_of_eq_bot _ _ _ (hba.boundedAbove k _ hN)]

/-- Bounded filtrations satisfy Mittag-Leffler. -/
theorem Filtration.IsBounded.toIsMittagLeffler {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBounded) : fil.IsMittagLeffler :=
  hb.toIsBoundedAbove.toIsMittagLeffler

end KIP126.Core.SpectralSequence
