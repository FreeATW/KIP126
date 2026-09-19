import KIP126.Def.Algebra.Truncation.Data

/-! Proofs and transition laws for the canonical truncation adapter. -/

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

namespace Filtration

/-- A truncation is bounded above by its quotient level. -/
def quotientFiltration_boundedAbove (fil : Filtration A) (q : ℤ) :
    (fil.quotientFiltration q).IsBoundedAbove := by
  refine { upper := fun _ => q, eq_bot_of_le := ?_ }
  intro i s hs
  change imageSubobject ((fil.F s i).arrow ≫
    cokernel.π (fil.F (q) i).arrow) = ⊥
  have hmono : fil.F s i ≤ fil.F (q) i := by
    exact fil.le_of_le (by omega) i
  have hzero : (fil.F s i).arrow ≫ cokernel.π (fil.F (q) i).arrow = 0 := by
    rw [show (fil.F s i).arrow =
      Subobject.ofLE _ _ hmono ≫ (fil.F (q) i).arrow
      from by rw [Subobject.ofLE_arrow]]
    rw [Category.assoc, cokernel.condition, comp_zero]
  simp only [hzero, imageSubobject_zero]

/-- If the source filtration is bounded below, its truncation is bounded. -/
noncomputable def quotientFiltration_isBounded
    {fil : Filtration A} (hbb : fil.IsBoundedBelow) (q : ℤ) :
    (fil.quotientFiltration q).IsBounded := by
  refine
    { lower := fun i => min (hbb.lower i) (q)
      upper := fun _ => q
      lower_le_upper := fun _ => min_le_right _ _
      eq_top_of_le := ?_
      eq_bot_of_le := ?_ }
  · intro i s hs
    have hs' : s ≤ hbb.lower i := le_trans hs (min_le_left _ _)
    have htop : fil.F s i = ⊤ := hbb.eq_top_of_le i s hs'
    have hiso : IsIso (fil.F s i).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).mpr htop
    change imageSubobject ((fil.F s i).arrow ≫
      cokernel.π (fil.F (q) i).arrow) = ⊤
    rw [imageSubobject_iso_comp]
    have h1 : Epi (image.ι (cokernel.π (fil.F (q) i).arrow)) :=
      epi_of_epi_fac (image.fac _)
    have h2 : IsIso (image.ι (cokernel.π (fil.F (q) i).arrow)) :=
      isIso_of_mono_of_epi _
    rw [← Subobject.isIso_arrow_iff_eq_top]
    have harr : (imageSubobject (cokernel.π (fil.F (q) i).arrow)).arrow =
        (imageSubobjectIso _).hom ≫ image.ι _ := by
      simp [imageSubobject_arrow]
    rw [harr]
    infer_instance
  · exact (fil.quotientFiltration_boundedAbove q).eq_bot_of_le

end Filtration

end KIP126.Core.Algebra
