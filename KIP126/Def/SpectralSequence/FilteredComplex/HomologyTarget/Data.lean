import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs

/-!
# Historical homology target of a filtered complex

The current KIP126 homology target uses Mathlib's normalized chain degrees.
This layer retains the definitionally indexed target used by the historical
weak-convergence proof, without changing the canonical `homologyObj` API.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- The historical presentation of the homology object at degree `k`. -/
@[reducible] noncomputable def homologySSObj (FC : FilteredComplex C) (k : ℤ) : C :=
  (ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1))
    (FC.d_comp_d (k + 1))).homology

/-- The filtration on the historical homology presentation used by the
nested-subobject convergence construction. -/
noncomputable def homologySSFiltration (FC : FilteredComplex C) :
    Filtration FC.homologySSObj where
  F := fun s k =>
    let S := ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1))
      (FC.d_comp_d (k + 1))
    let I := kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1)
    let h_zero : I.arrow ≫ S.g = 0 := by
      rw [show I.arrow = Subobject.ofLE I (kernelSubobject S.g)
          inf_le_left ≫ (kernelSubobject S.g).arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    imageSubobject (S.liftCycles I.arrow h_zero ≫ S.homologyπ)
  mono := fun s k => by
    dsimp only []
    set S := ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1))
      (FC.d_comp_d (k + 1))
    set I1 := kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1)
    set I0 := kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1)
    have hle : I1 ≤ I0 := inf_le_inf_left _ (FC.fil_anti s (k + 1 - 1))
    have h_zero_1 : I1.arrow ≫ S.g = 0 := by
      rw [show I1.arrow = Subobject.ofLE I1 (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have h_zero_0 : I0.arrow ≫ S.g = 0 := by
      rw [show I0.arrow = Subobject.ofLE I0 (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have hlift : S.liftCycles I1.arrow h_zero_1 =
        Subobject.ofLE I1 I0 hle ≫ S.liftCycles I0.arrow h_zero_0 := by
      apply (cancel_mono S.iCycles).mp
      rw [S.liftCycles_i, Category.assoc, S.liftCycles_i]
      exact (Subobject.ofLE_arrow hle).symm
    have hlift2 : S.liftCycles I1.arrow h_zero_1 ≫ S.homologyπ =
        Subobject.ofLE I1 I0 hle ≫
          (S.liftCycles I0.arrow h_zero_0 ≫ S.homologyπ) := by
      rw [← Category.assoc, hlift]
    conv_lhs => rw [show S.liftCycles I1.arrow _ ≫ S.homologyπ =
      Subobject.ofLE I1 I0 hle ≫
        (S.liftCycles I0.arrow _ ≫ S.homologyπ) from hlift2]
    exact imageSubobject_comp_le _ _

end FilteredComplex

end KIP126.Core.SpectralSequence
