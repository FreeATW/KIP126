import KIP126.Def.SpectralSequence.Basic.Proofs

/-!
# Successor-page homology identification

This construction is separated from the foundational records because it uses
the quotient and image lemmas proved in `Basic.Proofs`.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits
open PageHomology

universe u v w

set_option linter.dupNamespace false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-- The homology of page `r` at grading `k` is canonically isomorphic to page `r + 1`. -/
noncomputable def SpectralSequence.pageHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    E.Page (r + 1) k ≅ (E.pageShortComplex r (k - E.diffDeg r)).homology := by
  set n := (r - E.r₀).toNat with hn_def
  have hn1 : (r + 1 - E.r₀).toNat = n + 1 := by omega
  set S := E.pageShortComplex r (k - E.diffDeg r) with hS_def
  set k' := k - E.diffDeg r + E.diffDeg r
  set D' := E.ssData k'
  have hk_eq : k' = k := sub_add_cancel k (E.diffDeg r)
  have hBn_le_Bn1 : D'.B ↑n ≤ D'.B ↑(n + 1) :=
    D'.B_mono (by exact_mod_cast Nat.le_succ n)
  have hBn1_le_Zn1 : D'.B ↑(n + 1) ≤ D'.Z ↑(n + 1) := D'.B_le_Z _
  have hZn1_le_Zn : D'.Z ↑(n + 1) ≤ D'.Z ↑n :=
    D'.Z_anti (by exact_mod_cast Nat.le_succ n)
  have hBn_le_Zn1 : D'.B ↑n ≤ D'.Z ↑(n + 1) :=
    le_trans hBn_le_Bn1 hBn1_le_Zn1
  set i := Subobject.cokernelMap_ofLE
    (D'.B ↑n) (D'.Z ↑(n + 1)) (D'.Z ↑n)
    hBn_le_Zn1 hZn1_le_Zn with hi_def
  set π_map := Subobject.cokernelDesc_ofLE
    (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
    hBn_le_Bn1 hBn1_le_Zn1 with hπ_def
  have wi : i ≫ S.g = 0 := by
    apply comp_eq_zero_of_image_le_kernel
    change imageSubobject i ≤ kernelSubobject (E.d r k')
    rw [E.Z_succ r k' hr,
      show Subobject.ofLE (D'.Z ↑(n + 1)) (D'.Z ↑n)
          (D'.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ D'.pageπ ↑n =
        cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1) ≫ i
        from factor_cokernelMap _ _ _ _ _,
      imageSubobject_epi_comp]
  have heq_sub : Subobject.mk i = Subobject.mk (kernel.ι (E.d r k')) := by
    change Subobject.mk i = kernelSubobject (E.d r k')
    rw [E.Z_succ r k' hr,
      show Subobject.ofLE (D'.Z ↑(n + 1)) (D'.Z ↑n)
          (D'.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ D'.pageπ ↑n =
        cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1) ≫ i
        from factor_cokernelMap _ _ _ _ _,
      imageSubobject_epi_comp, imageSubobject_mono]
  have hi : IsLimit (KernelFork.ofι i wi) := by
    apply (kernelIsKernel (E.d r k')).ofIsoLimit
    exact Fork.ext (Subobject.isoOfMkEqMk i (kernel.ι (E.d r k')) heq_sub).symm
      (Subobject.ofMkLEMk_comp heq_sub.ge)
  set j := Subobject.cokernelMap_ofLE
    (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
    hBn_le_Bn1 hBn1_le_Zn1 with hj_def
  set f_lift := hi.lift (KernelFork.ofι S.f (by exact S.zero)) with hf_lift_def
  have hj_π : j ≫ π_map = 0 := by
    simp only [j, π_map, Subobject.cokernelMap_ofLE, Subobject.cokernelDesc_ofLE]
    ext
    simp only [cokernel.π_desc_assoc, cokernel.π_desc, comp_zero,
      Category.assoc, cokernel.condition]
  have hBn_le_Zn : D'.B ↑(n + 1) ≤ D'.Z ↑n :=
    le_trans hBn1_le_Zn1 hZn1_le_Zn
  have hfactor :
      Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn ≫ D'.pageπ ↑n =
        cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.B ↑(n + 1)) hBn_le_Bn1) ≫
          j ≫ i := by
    change Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn ≫
      cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑n) (D'.B_le_Z ↑n)) = _
    rw [(Subobject.ofLE_comp_ofLE
      (D'.B ↑(n + 1)) (D'.Z ↑(n + 1)) (D'.Z ↑n)
      hBn1_le_Zn1 hZn1_le_Zn).symm,
      Category.assoc,
      factor_cokernelMap
        (D'.B ↑n) (D'.Z ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn1 hZn1_le_Zn,
      ← Category.assoc
        (Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑(n + 1)) hBn1_le_Zn1),
      factor_cokernelMap
        (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
        hBn_le_Bn1 hBn1_le_Zn1,
      Category.assoc]
  have hfi : f_lift ≫ i = S.f :=
    hi.fac (KernelFork.ofι S.f (by exact S.zero)) WalkingParallelPair.zero
  have hB := E.B_succ r (k - E.diffDeg r) hr
  have him : imageSubobject (f_lift ≫ i) = imageSubobject (j ≫ i) := by
    rw [hfi]
    change imageSubobject (E.d r (k - E.diffDeg r)) = _
    rw [hB, hfactor, imageSubobject_epi_comp]
  have hjim : imageSubobject (j ≫ i) = Subobject.mk (j ≫ i) :=
    imageSubobject_mono _
  have hle : imageSubobject (f_lift ≫ i) ≤ Subobject.mk (j ≫ i) :=
    him ▸ hjim ▸ le_refl _
  have hfact_ji : (Subobject.mk (j ≫ i)).Factors (f_lift ≫ i) := by
    apply Subobject.factors_of_le _ hle
    have hself := imageSubobject_factors_comp_self (f := f_lift ≫ i) (𝟙 _)
    simpa using hself
  set φ_ji := (Subobject.mk (j ≫ i)).factorThru (f_lift ≫ i) hfact_ji
  have hφ_ji : φ_ji ≫ (Subobject.mk (j ≫ i)).arrow = f_lift ≫ i :=
    Subobject.factorThru_arrow _ _ _
  have harrow_ji : (Subobject.mk (j ≫ i)).arrow =
      (Subobject.underlyingIso (j ≫ i)).hom ≫ (j ≫ i) :=
    (Subobject.underlyingIso_hom_comp_eq_mk (j ≫ i)).symm
  set ψ := φ_ji ≫ (Subobject.underlyingIso (j ≫ i)).hom with hψ_def
  have hψ_j : ψ ≫ j = f_lift := by
    apply (cancel_mono i).mp
    rw [Category.assoc]
    change ψ ≫ (j ≫ i) = f_lift ≫ i
    change (φ_ji ≫ (Subobject.underlyingIso (j ≫ i)).hom) ≫ (j ≫ i) = f_lift ≫ i
    rw [Category.assoc, ← harrow_ji, hφ_ji]
  have wπ : f_lift ≫ π_map = 0 := by
    calc
      f_lift ≫ π_map = (ψ ≫ j) ≫ π_map := by rw [hψ_j]
      _ = ψ ≫ (j ≫ π_map) := by rw [Category.assoc]
      _ = ψ ≫ 0 := by rw [hj_π]
      _ = 0 := comp_zero
  have hπ : IsColimit (CokernelCofork.ofπ π_map wπ) := by
    have hφ_eq : φ_ji = factorThruImageSubobject (f_lift ≫ i) ≫
        (Subobject.isoOfEq _ _ (him.trans hjim)).hom := by
      apply (cancel_mono (Subobject.mk (j ≫ i)).arrow).mp
      rw [hφ_ji, Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow,
        imageSubobject_arrow_comp]
    have hψ_epi : Epi ψ := by
      rw [hψ_def, hφ_eq, Category.assoc]
      exact epi_comp _ _
    have hπ_factor : cokernel.π j ≫
        (Subobject.thirdIso
          (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
          hBn_le_Bn1 hBn1_le_Zn1).hom = π_map :=
      cokernel.π_desc _ _ _
    set thirdIso := Subobject.thirdIso
      (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
      hBn_le_Bn1 hBn1_le_Zn1 with hthirdIso_def
    have hjs : ∀ (s : Cofork f_lift 0), j ≫ Cofork.π s = 0 := by
      intro s
      haveI := hψ_epi
      apply zero_of_epi_comp ψ
      rw [← Category.assoc, hψ_j]
      have hs := s.condition
      simp only [zero_comp] at hs
      exact hs
    exact Cofork.IsColimit.mk _
      (fun s => thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s))
      (fun s => by
        change π_map ≫ thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s) =
          Cofork.π s
        rw [show π_map = cokernel.π j ≫ thirdIso.hom from hπ_factor.symm,
          Category.assoc, thirdIso.hom_inv_id_assoc, cokernel.π_desc])
      (fun s m hm => by
        change m = thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s)
        rw [← cancel_epi thirdIso.hom, thirdIso.hom_inv_id_assoc]
        apply (cancel_epi (cokernel.π j)).mp
        rw [cokernel.π_desc, ← Category.assoc, hπ_factor]
        exact hm)
  set h : S.LeftHomologyData := {
    K := cokernel (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1)
    H := D'.page ↑(n + 1)
    i := i
    π := π_map
    wi := wi
    hi := hi
    wπ := wπ
    hπ := hπ
  }
  have hPageH : E.Page (r + 1) k = h.H := by
    change (E.ssData k).page ↑((r + 1 - E.r₀).toNat) = D'.page ↑(n + 1)
    rw [hn1]
    congr 1
    exact hk_eq.symm ▸ rfl
  exact eqToIso hPageH ≪≫ h.homologyIso.symm

end KIP126.Core.SpectralSequence
