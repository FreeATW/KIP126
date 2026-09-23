import KIP126.Def.Algebra.Completion.Data

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

namespace Filtration

namespace CompletionWitness

variable {F : Filtration A} {i : ι}

/-- A completion witness supplies existence of the corresponding quotient
tower limit; callers can install this result as a local `HasLimit` instance. -/
theorem hasLimit (W : CompletionWitness F i) : HasLimit (F.quotientTower i) :=
  HasLimit.mk ⟨F.quotientTowerCone i, W.isLimit⟩

/-- The induced isomorphism from a complete filtered component to the limit
of its quotient tower. -/
noncomputable def completionIso (W : CompletionWitness F i)
    [HasLimit (F.quotientTower i)] :
    A i ≅ limit (F.quotientTower i) :=
  W.isLimit.conePointUniqueUpToIso (limit.isLimit _)

/-- The completion isomorphism is the canonical map to the limit, as
characterized by all quotient projections. -/
@[reassoc]
lemma completionIso_hom_comp_limit_π (W : CompletionWitness F i)
    [HasLimit (F.quotientTower i)] (s : OrderDual ℤ) :
    W.completionIso.hom ≫ limit.π (F.quotientTower i) s =
      F.quotientProjection s i :=
  IsLimit.conePointUniqueUpToIso_hom_comp W.isLimit (limit.isLimit _) s

end CompletionWitness

/-- Once a decreasing filtration is zero at level `t`, it is zero at every
higher level `s`. -/
lemma eq_bot_of_le_of_eq_bot (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι)
    (ht : F.F t i = ⊥) : F.F s i = ⊥ := by
  apply le_antisymm
  · rw [← ht]
    exact F.le_of_le h i
  · exact bot_le

/-- At a zero filtration level, the quotient projection is an isomorphism. -/
lemma quotientProjection_isIso_of_eq_bot (F : Filtration A) (s : ℤ) (i : ι)
    (h : F.F s i = ⊥) : IsIso (F.quotientProjection s i) := by
  change IsIso (cokernel.π (F.F s i).arrow)
  rw [h, Subobject.bot_arrow]
  infer_instance

/-- A quotient transition between two zero filtration levels is an
isomorphism. -/
lemma quotientTransition_isIso_of_eq_bot (F : Filtration A) {t s : ℤ}
    (h : t ≤ s) (i : ι) (hs : F.F s i = ⊥) (ht : F.F t i = ⊥) :
    IsIso (F.quotientTransition h i) := by
  letI : IsIso (F.quotientProjection s i) :=
    F.quotientProjection_isIso_of_eq_bot s i hs
  letI : IsIso (F.quotientProjection t i) :=
    F.quotientProjection_isIso_of_eq_bot t i ht
  exact IsIso.of_isIso_fac_left (F.quotientProjection_transition h i)

/-- A filtration which is zero at level `u` yields a quotient tower that is
eventually constant towards `u`. -/
lemma quotientTower_isEventuallyConstantTo_of_eq_bot (F : Filtration A) (i : ι)
    (u : ℤ) (hu : F.F u i = ⊥) :
    (F.quotientTower i).IsEventuallyConstantTo (OrderDual.toDual u) := by
  intro s f
  change IsIso (F.quotientTransition f.le i)
  exact F.quotientTransition_isIso_of_eq_bot f.le i
    (F.eq_bot_of_le_of_eq_bot f.le i hu) hu

/-- If one filtration level is zero, then the canonical quotient cone is a
limit cone. -/
noncomputable def quotientTowerCone_isLimit_of_eq_bot (F : Filtration A) (i : ι)
    (u : ℤ) (hu : F.F u i = ⊥) : IsLimit (F.quotientTowerCone i) := by
  let h := F.quotientTower_isEventuallyConstantTo_of_eq_bot i u hu
  letI : IsIso ((F.quotientTowerCone i).π.app (OrderDual.toDual u)) := by
    change IsIso (F.quotientProjection u i)
    exact F.quotientProjection_isIso_of_eq_bot u i hu
  exact h.isLimitOfIsIso (F.quotientTowerCone i)

namespace CompletionWitness

variable {F : Filtration A} {i : ι}

/-- A degreewise eventually-zero decreasing filtration is complete with
respect to its canonical quotient tower. -/
noncomputable def of_isEventuallyZero (F : Filtration A)
    (hF : F.IsEventuallyZero) (i : ι) : CompletionWitness F i := by
  let u : ℤ := Classical.choose (hF i)
  exact ⟨F.quotientTowerCone_isLimit_of_eq_bot i u
    (Classical.choose_spec (hF i))⟩

/-- A degreewise bounded-above filtration is complete with respect to its
canonical quotient tower. -/
noncomputable def of_isBoundedAbove (F : Filtration A)
    (hF : F.IsBoundedAbove) (i : ι) : CompletionWitness F i :=
  of_isEventuallyZero F hF.isEventuallyZero i

end CompletionWitness

end Filtration

end KIP126.Core.Algebra
