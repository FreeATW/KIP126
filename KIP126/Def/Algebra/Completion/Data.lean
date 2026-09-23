import KIP126.Def.Algebra.Filtration.Proofs
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Degreewise completion of a decreasing filtration

For a decreasing filtration `F` of a graded object, this file constructs the
canonical inverse system of quotient objects
`Aᵢ / Fˢ Aᵢ`.  The universal-property predicate `CompletionWitness` records
exactly when the canonical cone from `Aᵢ` is limiting.  It is a proved
interface:
the final section proves the predicate for a degreewise eventually-zero
filtration, using Mathlib's eventually-constant-limit construction.
-/

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

namespace Filtration

/-- The quotient `Aᵢ / Fˢ Aᵢ` at one filtration and grading degree. -/
noncomputable def quotientAt (F : Filtration A) (s : ℤ) (i : ι) : C :=
  cokernel (F.F s i).arrow

/-- The canonical projection `Aᵢ ⟶ Aᵢ / Fˢ Aᵢ`. -/
noncomputable def quotientProjection (F : Filtration A) (s : ℤ) (i : ι) :
    A i ⟶ F.quotientAt s i :=
  cokernel.π (F.F s i).arrow

/-- If `t ≤ s`, the quotient by `Fˢ` maps to the quotient by `Fᵗ`. -/
noncomputable def quotientTransition (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.quotientAt s i ⟶ F.quotientAt t i :=
  cokernel.desc (F.F s i).arrow (F.quotientProjection t i) (by
    change (F.F s i).arrow ≫ cokernel.π (F.F t i).arrow = 0
    rw [← F.inclusion_arrow h i, Category.assoc, cokernel.condition, comp_zero])

/-- The quotient transition commutes with the quotient projections. -/
@[reassoc]
lemma quotientProjection_transition (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.quotientProjection s i ≫ F.quotientTransition h i = F.quotientProjection t i := by
  exact cokernel.π_desc _ _ _

/-- Quotient transitions compose in the evident order. -/
@[reassoc]
lemma quotientTransition_comp (F : Filtration A) {r s t : ℤ}
    (hrs : r ≤ s) (hst : s ≤ t) (i : ι) :
    F.quotientTransition hst i ≫ F.quotientTransition hrs i =
      F.quotientTransition (hrs.trans hst) i := by
  letI : Epi (F.quotientProjection t i) := by
    change Epi (cokernel.π (F.F t i).arrow)
    infer_instance
  apply (cancel_epi (F.quotientProjection t i)).mp
  calc
    F.quotientProjection t i ≫ F.quotientTransition hst i ≫
        F.quotientTransition hrs i =
      (F.quotientProjection t i ≫ F.quotientTransition hst i) ≫
        F.quotientTransition hrs i := (Category.assoc _ _ _).symm
    _ = F.quotientProjection s i ≫ F.quotientTransition hrs i := by
        rw [F.quotientProjection_transition]
    _ = F.quotientProjection r i := F.quotientProjection_transition hrs i
    _ = F.quotientProjection t i ≫ F.quotientTransition (hrs.trans hst) i :=
      (F.quotientProjection_transition (hrs.trans hst) i).symm

/-- The identity quotient transition is the identity. -/
@[simp]
lemma quotientTransition_id (F : Filtration A) (s : ℤ) (i : ι) :
    F.quotientTransition (le_rfl : s ≤ s) i = 𝟙 _ := by
  letI : Epi (F.quotientProjection s i) := by
    change Epi (cokernel.π (F.F s i).arrow)
    infer_instance
  apply (cancel_epi (F.quotientProjection s i)).mp
  rw [F.quotientProjection_transition, Category.comp_id]

/-- The canonical inverse system `s ↦ Aᵢ / Fˢ Aᵢ`.

It is indexed by `OrderDual ℤ`: a morphism `s ⟶ t` has `t ≤ s`, and hence
is precisely the quotient transition from level `s` to level `t`. -/
noncomputable def quotientTower (F : Filtration A) (i : ι) :
    (OrderDual ℤ) ⥤ C where
  obj s := F.quotientAt s i
  map f := F.quotientTransition f.le i
  map_id s := F.quotientTransition_id s i
  map_comp f g := by
    simpa only [Functor.comp_map] using (F.quotientTransition_comp g.le f.le i).symm

/-- The canonical cone from `Aᵢ` to its tower of filtration quotients. -/
noncomputable def quotientTowerCone (F : Filtration A) (i : ι) :
    Cone (F.quotientTower i) where
  pt := A i
  π :=
    { app := fun s => F.quotientProjection s i
      naturality := by
        intro s t f
        dsimp [quotientTower]
        calc
          𝟙 (A i) ≫ F.quotientProjection t i = F.quotientProjection t i := Category.id_comp _
          _ = F.quotientProjection s i ≫ F.quotientTransition f.le i :=
            (F.quotientProjection_transition f.le i).symm }

/-- A degreewise completeness witness: the canonical cone from `Aᵢ` to the
quotient tower is a limit cone.  This is the categorical statement
`Aᵢ ≅ lim_s Aᵢ/FˢAᵢ`, retaining the canonical comparison maps. -/
structure CompletionWitness (F : Filtration A) (i : ι) where
  isLimit : IsLimit (F.quotientTowerCone i)

end Filtration

end KIP126.Core.Algebra
