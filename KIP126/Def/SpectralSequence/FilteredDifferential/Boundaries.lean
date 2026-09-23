import KIP126.Def.SpectralSequence.FilteredDifferential.Helpers
import KIP126.Def.SpectralSequence.FilteredPage.Proofs

/-! The next boundary subobject gives the image of the finite-page differential. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

open DifferentialHelpers

set_option maxHeartbeats 400000 in
/-- The image of the finite-page differential is the page image of the next
    boundary subobject included in the current cycle subobject.  This is the
    canonical finite-page `B_succ` relation, adapted from the historical
    filtered-complex proof. -/
theorem pageDifferential_B_succ (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    imageSubobject (FC.pageDifferential s k n) =
      imageSubobject (Subobject.ofLE
        (FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1))
        (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)
        (le_trans (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑(n + 1))
          (FC.cycleSubobject_antitone (s + ↑n) (k - 1)
            (by exact_mod_cast Nat.le_succ n))) ≫
        FC.pageπ (s + ↑n) (k - 1) ↑n) := by
  -- === Reconstruct the internal abbreviations of pageDifferential ===
  set ι_s := Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k) with hι_s_def
  set πV := FC.filtration.toAssociatedGraded s k with hπV_def
  set f_n := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) with hf_n_def
  set kerZ := kernelSubobject f_n with hkerZ_def
  set ι_t := Subobject.ofLE (FC.filtration.F (s + ↑n + 1) (k - 1)) (FC.filtration.F (s + ↑n) (k - 1))
    (FC.filtration.decreasing (s + ↑n) (k - 1)) with hι_t_def
  set πV' := FC.filtration.toAssociatedGraded (s + ↑n) (k - 1) with hπV'_def
  set f_n' := (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) with hf_n'_def
  set kerZ' := kernelSubobject f_n' with hkerZ'_def
  -- Reconstruct lift_n, lift_to_kerZ', to_Z_n_t, ψ, p, h_on_Zn
  have h_ker_fn : kerZ.arrow ≫ f_n = 0 := kernelSubobject_arrow_comp f_n
  have h_factor_zero : (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc] at h_ker_fn ⊢; exact h_ker_fn
  set lift_n := Abelian.monoLift (FC.filtration.F (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) h_factor_zero with hlift_n_def
  have h_lift_spec : lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
      kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := Abelian.monoLift_comp _ _ _
  have h_lift_in_kerZ' : lift_n ≫ f_n' = 0 := by
    calc lift_n ≫ f_n'
        = ((lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫ FC.complex.d (k - 1) (k - 1 - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          simp only [hf_n'_def, Category.assoc]
      _ = ((kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫ FC.complex.d (k - 1) (k - 1 - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by rw [h_lift_spec]
      _ = 0 := by
          rw [show (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫ FC.complex.d (k - 1) (k - 1 - 1) =
            kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ (FC.complex.d k (k - 1) ≫ FC.complex.d (k - 1) (k - 1 - 1)) from by
            simp only [Category.assoc], FC.complex.d_comp_d k]; simp only [comp_zero, zero_comp]
  set lift_to_kerZ' := factorThruKernelSubobject f_n' lift_n h_lift_in_kerZ'
    with hlift_to_kerZ'_def
  have h_ltk_spec : lift_to_kerZ' ≫ kerZ'.arrow = lift_n :=
    factorThruKernelSubobject_comp_arrow f_n' lift_n h_lift_in_kerZ'
  set to_Z_n_t := lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')
    with hto_Z_n_t_def
  let ψ := to_Z_n_t ≫ FC.pageπ (s + ↑n) (k - 1) ↑n
  have hψ_def : ψ = to_Z_n_t ≫ FC.pageπ (s + ↑n) (k - 1) ↑n := rfl
  let p := factorThruImageSubobject (kerZ.arrow ≫ πV)
  have hp_def : p = factorThruImageSubobject (kerZ.arrow ≫ πV) := rfl
  haveI : Epi p := inferInstance
  -- h_ker_p_ψ : kernel.ι p ≫ ψ = 0 (from pageDifferential construction)
  -- We need this for epiDesc. Reconstruct the proof.
  have h_ker_p_ψ : kernel.ι p ≫ ψ = 0 := by
    -- This follows the same proof as in pageDifferential (lines 699-908).
    -- kernel.ι p ≫ to_Z_n_t factors through ofLE(B_n_t, Z_n_t), and cokernel kills it.
    set B_n_t' := FC.boundarySubobject (s + ↑n) (k - 1) ↑n
    set Z_n_t' := FC.cycleSubobject (s + ↑n) (k - 1) ↑n
    have hB_le_Z' := FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n
    -- to_Z_n_t ≫ Z_n_t'.arrow = lift_n ≫ πV'
    have h_to_Z_comp' : to_Z_n_t ≫ Z_n_t'.arrow = lift_n ≫ πV' := by
      change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
        (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
      simp only [Category.assoc, imageSubobject_arrow_comp]
      rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
        (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm, h_ltk_spec]
    -- kernel.ι p ≫ lift_n ≫ πV' factors through B_n_t'
    have h_comp_eq' : kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
        kernel.ι p ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
      simp only [h_lift_spec]
    set imgD' := imageSubobject ((FC.filtration.F (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1))
    have h_fac_imgD' : imgD'.Factors
        (kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
      rw [h_comp_eq']
      have h1 : kernel.ι p ≫ (kerZ.arrow ≫ πV) = 0 := by
        have h_p_Z : p ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow = kerZ.arrow ≫ πV :=
          imageSubobject_arrow_comp (kerZ.arrow ≫ πV)
        calc kernel.ι p ≫ (kerZ.arrow ≫ πV)
            = kernel.ι p ≫ (p ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow) := by rw [h_p_Z]
          _ = (kernel.ι p ≫ p) ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow := by
              simp only [Category.assoc]
          _ = 0 ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow := by rw [kernel.condition]
          _ = 0 := zero_comp
      have h1' : (kernel.ι p ≫ kerZ.arrow) ≫ cokernel.π ι_s = 0 := by
        rw [Category.assoc]; exact h1
      set α' := Abelian.monoLift ι_s (kernel.ι p ≫ kerZ.arrow) h1'
      have hα'_spec : α' ≫ ι_s = kernel.ι p ≫ kerZ.arrow := Abelian.monoLift_comp _ _ _
      have h_ι_arrow' : ι_s ≫ (FC.filtration.F s k).arrow = (FC.filtration.F (s + 1) k).arrow :=
        Subobject.ofLE_arrow (FC.filtration.decreasing s k)
      have h_rewrite' : kernel.ι p ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
          α' ≫ ((FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1)) := by
        conv_lhs => rw [show kernel.ι p ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
          ((kernel.ι p ≫ kerZ.arrow) ≫ (FC.filtration.F s k).arrow) ≫ FC.complex.d k (k - 1) from by
          simp only [Category.assoc]]
        rw [← hα'_spec, show (α' ≫ ι_s) ≫ (FC.filtration.F s k).arrow = α' ≫ (ι_s ≫ (FC.filtration.F s k).arrow) from
          Category.assoc _ _ _, h_ι_arrow', Category.assoc]
      rw [h_rewrite']
      apply Subobject.factors_of_factors_right
      have h_transport' : eqToHom (show Subobject.underlying.obj (FC.filtration.F (s + 1) k) =
          Subobject.underlying.obj (FC.filtration.F (s + 1) ((k - 1) + 1)) by
          rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
          ((FC.filtration.F (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
          (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) :=
        eqToHom_arrow_dToK_local FC (s + 1) k
      rw [← h_transport', Subobject.mk_factors_iff]
      exact ⟨eqToHom (by rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
        factorThruImage ((FC.filtration.F (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)), by simp⟩
    have h_fac_fil' : (FC.filtration.F (s + ↑n) (k - 1)).Factors
        (kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) :=
      Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow lift_n)
    set I' := imgD' ⊓ FC.filtration.F (s + ↑n) (k - 1)
    have h_fac_I' : I'.Factors (kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) :=
      (Subobject.inf_factors _).mpr ⟨h_fac_imgD', h_fac_fil'⟩
    set δ' := I'.factorThru _ h_fac_I'
    have hδ'_spec : δ' ≫ I'.arrow = kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow :=
      Subobject.factorThru_arrow _ _ _
    have h_δ'_ofLE : δ' ≫ Subobject.ofLE I' (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right =
        kernel.ι p ≫ lift_n := by
      apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
      rw [Category.assoc, Subobject.ofLE_arrow, hδ'_spec]
      simp only [Category.assoc]
    have h_imgD_bnd' : imageSubobject ((FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) = imgD' := by
      rw [show (s : ℤ) + (↑n : ℤ) - (↑n : ℤ) + 1 = s + 1 from by omega]
    have h_I_bnd' : imageSubobject ((FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) ⊓ FC.filtration.F (s + ↑n) (k - 1) = I' := by
      rw [h_imgD_bnd']
    have h_bnd_fac' : B_n_t'.Factors (kernel.ι p ≫ lift_n ≫ πV') := by
      rw [show kernel.ι p ≫ lift_n ≫ πV' = (kernel.ι p ≫ lift_n) ≫ πV'
        from (Category.assoc _ _ _).symm, ← h_δ'_ofLE, Category.assoc]
      apply Subobject.factors_of_factors_right
      set I_bnd' := imageSubobject ((FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) ⊓ FC.filtration.F (s + ↑n) (k - 1)
      have h_I_le_Ibnd' : I' ≤ I_bnd' := le_of_eq h_I_bnd'.symm
      have h_ofLE_factor' : Subobject.ofLE I' (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right =
          Subobject.ofLE I' I_bnd' h_I_le_Ibnd' ≫
          Subobject.ofLE I_bnd' (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right := by
        apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
        simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [h_ofLE_factor', Category.assoc]
      apply Subobject.factors_of_factors_right
      change (imageSubobject
        (Subobject.ofLE I_bnd' (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right ≫ πV')).Factors
        (Subobject.ofLE I_bnd' (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right ≫ πV')
      rw [Subobject.mk_factors_iff]
      exact ⟨factorThruImage _, by simp⟩
    -- Factor kernel.ι p ≫ to_Z_n_t through ofLE(B_n_t', Z_n_t')
    have h_ker_to_Z_fac' : B_n_t'.Factors (kernel.ι p ≫ to_Z_n_t ≫ Z_n_t'.arrow) := by
      rw [h_to_Z_comp']; exact h_bnd_fac'
    set γ' := B_n_t'.factorThru _ h_ker_to_Z_fac'
    have hγ'_spec : γ' ≫ B_n_t'.arrow = kernel.ι p ≫ to_Z_n_t ≫ Z_n_t'.arrow :=
      Subobject.factorThru_arrow _ _ _
    have h_factor_B' : kernel.ι p ≫ to_Z_n_t =
        γ' ≫ Subobject.ofLE B_n_t' Z_n_t' hB_le_Z' := by
      apply (inferInstance : Mono Z_n_t'.arrow).right_cancellation
      calc
        (kernel.ι p ≫ to_Z_n_t) ≫ Z_n_t'.arrow =
            kernel.ι p ≫ to_Z_n_t ≫ Z_n_t'.arrow := Category.assoc _ _ _
        _ = γ' ≫ B_n_t'.arrow := hγ'_spec.symm
        _ = (γ' ≫ Subobject.ofLE B_n_t' Z_n_t' hB_le_Z') ≫ Z_n_t'.arrow := by
          rw [Category.assoc, Subobject.ofLE_arrow]
    have h_cok' : Subobject.ofLE B_n_t' Z_n_t' hB_le_Z' ≫ FC.pageπ (s + ↑n) (k - 1) ↑n = 0 := by
      rw [FilteredComplex.pageπ]
      exact cokernel.condition _
    rw [hψ_def]
    calc kernel.ι p ≫ to_Z_n_t ≫ FC.pageπ (s + ↑n) (k - 1) ↑n
        = (kernel.ι p ≫ to_Z_n_t) ≫ FC.pageπ (s + ↑n) (k - 1) ↑n := (Category.assoc _ _ _).symm
      _ = (γ' ≫ Subobject.ofLE B_n_t' Z_n_t' hB_le_Z') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n := by rw [h_factor_B']; rfl
      _ = γ' ≫ (Subobject.ofLE B_n_t' Z_n_t' hB_le_Z' ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) := Category.assoc _ _ _
      _ = γ' ≫ 0 := by rw [h_cok']
      _ = 0 := comp_zero
  set h_on_Zn := Abelian.epiDesc p ψ h_ker_p_ψ with hh_on_Zn_def
  -- h_on_Zn : Z_n_s.underlying → target page, with p ≫ h_on_Zn = ψ
  -- === Step 1: Reduce LHS ===
  -- pageDifferential = cokernel.desc(ofLE_source, h_on_Zn, h_B_zero)
  -- pageπ_source ≫ pageDifferential = h_on_Zn (cokernel.π_desc)
  -- pageπ_source is epi, so imageSubobject(pageDifferential) = imageSubobject(h_on_Zn)
  -- p ≫ h_on_Zn = ψ, p is epi, so imageSubobject(h_on_Zn) = imageSubobject(ψ)
  -- Therefore: imageSubobject(pageDifferential) = imageSubobject(ψ)
  -- Step 1a: Show pageDifferential matches cokernel.desc _ h_on_Zn _
  -- Need to reconstruct h_B_zero from pageDifferential definition.
  -- Instead of tracking h_B_zero, use a calc chain:
  -- imageSubobject(pageDiff) = imageSubobject(pageπ_s ≫ pageDiff) [epi_comp']
  --   = imageSubobject(h_on_Zn) [cokernel.π_desc]
  --   = imageSubobject(p ≫ h_on_Zn) [epi_comp']
  --   = imageSubobject(ψ) [comp_epiDesc]
  -- Use the approach: first show imageSubobject(pageDiff) = imageSubobject(ψ) indirectly.
  -- Approach: Use erw to access cokernel.π_desc and Abelian.comp_epiDesc, but
  -- contain pollution in a have block.
  have h_img_pageDiff_eq_ψ : imageSubobject (FC.pageDifferential s k n) =
      imageSubobject ψ := by
    -- Step 1: imageSubobject(pageπ_s ≫ pageDiff) = imageSubobject(pageDiff)
    set pageπ_s := FC.pageπ s k ↑n with hpageπ_s_def
    haveI : Epi pageπ_s := by
      change Epi (cokernel.π (Subobject.ofLE
        (FC.boundarySubobject s k ↑n) (FC.cycleSubobject s k ↑n)
        (FC.B_le_Z_aux s k ↑n)))
      infer_instance
    rw [← imageSubobject_epi_comp'_local pageπ_s (FC.pageDifferential s k n)]
    -- Goal: imageSubobject(pageπ_s ≫ pageDiff) = imageSubobject(ψ)
    -- Step 2: pageπ_s ≫ pageDiff = h_on_Zn
    erw [cokernel.π_desc]
    -- Goal: imageSubobject(h_on_Zn) = imageSubobject(ψ)
    -- Step 3: imageSubobject(p ≫ h_on_Zn) = imageSubobject(h_on_Zn)
    erw [← hh_on_Zn_def]
    erw [← imageSubobject_epi_comp'_local
      (factorThruImageSubobject (kerZ.arrow ≫ πV)) _]
    -- Goal: imageSubobject(p ≫ h_on_Zn) = imageSubobject(ψ)
    rw [Abelian.comp_epiDesc]
  rw [h_img_pageDiff_eq_ψ]
  -- Now goal: imageSubobject(ψ) = imageSubobject(ofLE(B_{n+1}, Z_n) ≫ FC.pageπ (s + ↑n) (k - 1) ↑n)
  -- === Step 2: Prove equality via le_antisymm ===
  apply le_antisymm
  -- === (≤) direction: imageSubobject(ψ) ≤ imageSubobject(ofLE(B_{n+1}, Z_n) ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) ===
  · -- ψ = to_Z_n_t ≫ FC.pageπ (s + ↑n) (k - 1) ↑n
    -- to_Z_n_t = lift_to_kerZ' ≫ factorThruImageSubobject(kerZ'.arrow ≫ πV')
    -- to_Z_n_t : kerZ.underlying → Z_n_t.underlying
    -- We show: to_Z_n_t factors through ofLE(B_{n+1}, Z_n) via a left factor.
    -- Specifically: to_Z_n_t = γ ≫ ofLE(B_{n+1}, Z_n) where
    -- γ = factorThruImageSubobject(something) ≫ factorThruImage(...) etc.
    -- Actually we need lift_n to factor through I_bnd, then through B_{n+1}.
    -- Key: lift_n ≫ (FC.filtration.F (s+↑n) (k-1)).arrow = kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ d(k)
    -- The d-image kerZ.arrow ≫ fil(s)(k).arrow ≫ d(k) is in imgD (via transport)
    -- Also lift_n itself witnesses it's in fil(s+n)(k-1).
    -- So lift_n ≫ fil(s+n).arrow factors through I_bnd = imgD ⊓ fil(s+n).
    -- Then lift_n ≫ πV' = factorThru_I ≫ oI_bnd ≫ πV'
    -- and oI_bnd ≫ πV' generates B_{n+1}.
    -- === Setup I_bnd (boundary) at (s+n, k-1) with index n+1 ===
    -- B_{n+1} = boundarySubobject (s+↑n) (k-1) ↑(n+1)
    -- imgD_bnd = imageSubobject(fil((s+↑n) - ↑(n+1) + 1)((k-1)+1).arrow ≫ dToK(k-1))
    -- Note: (s+↑n) - ↑(n+1) + 1 = s, so
    -- imgD_bnd = imageSubobject(fil(s)((k-1)+1).arrow ≫ dToK(k-1))
    set imgD_bnd := imageSubobject ((FC.filtration.F (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫
      FC.dToK (k - 1)) with himgD_bnd_def
    set I_bnd := imgD_bnd ⊓ FC.filtration.F (s + ↑n) (k - 1) with hI_bnd_def
    set oI_bnd := Subobject.ofLE I_bnd (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right
      with hoI_bnd_def
    -- B_{n+1} at target = imageSubobject(oI_bnd ≫ πV')
    -- Z_n at target = imageSubobject(kerZ'.arrow ≫ πV')
    let B_n1_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1)
    let Z_n_t := FC.cycleSubobject (s + ↑n) (k - 1) ↑n
    -- lift_n ≫ fil(s+n).arrow = kerZ.arrow ≫ fil(s).arrow ≫ d(k)
    -- This is in imgD_bnd because:
    -- fil(s).arrow ≫ d(k) = eqToHom ≫ fil(s)((k-1)+1).arrow ≫ dToK(k-1)
    -- and (s+↑n) - ↑(n+1) + 1 = s
    have h_idx_eq_s : (s : ℤ) + ↑n - ↑(n + 1) + 1 = s := by push_cast; omega
    -- imgD_bnd = imageSubobject(fil(s)((k-1)+1).arrow ≫ dToK(k-1))
    have h_imgD_eq : imgD_bnd =
        imageSubobject ((FC.filtration.F s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) := by
      rw [himgD_bnd_def, h_idx_eq_s]
    -- lift_n ≫ fil(s+n).arrow is in imgD_bnd
    have h_fac_imgD_bnd : imgD_bnd.Factors
        (lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
      rw [h_lift_spec]
      -- Goal: imgD_bnd.Factors(kerZ.arrow ≫ fil(s)(k).arrow ≫ d(k))
      rw [h_imgD_eq]
      have h_transport_dk : eqToHom (show Subobject.underlying.obj (FC.filtration.F s k) =
          Subobject.underlying.obj (FC.filtration.F s ((k - 1) + 1)) by
          rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
          ((FC.filtration.F s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
          (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) :=
        eqToHom_arrow_dToK_local FC s k
      rw [← h_transport_dk, Subobject.mk_factors_iff]
      exact ⟨kerZ.arrow ≫ eqToHom (by rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
        factorThruImage ((FC.filtration.F s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)), by simp⟩
    have h_fac_fil_bnd : (FC.filtration.F (s + ↑n) (k - 1)).Factors
        (lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) :=
      Subobject.factors_comp_arrow lift_n
    have h_fac_I_bnd : I_bnd.Factors (lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) :=
      (Subobject.inf_factors _).mpr ⟨h_fac_imgD_bnd, h_fac_fil_bnd⟩
    set δ_bnd := I_bnd.factorThru _ h_fac_I_bnd with hδ_bnd_def
    have hδ_bnd_spec : δ_bnd ≫ I_bnd.arrow = lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow :=
      Subobject.factorThru_arrow _ _ _
    -- δ_bnd ≫ oI_bnd = lift_n (by mono cancellation)
    have h_δ_oI : δ_bnd ≫ oI_bnd = lift_n := by
      apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
      rw [Category.assoc, Subobject.ofLE_arrow, hδ_bnd_spec]
    -- lift_n ≫ πV' = δ_bnd ≫ oI_bnd ≫ πV'
    have h_lift_πV' : lift_n ≫ πV' = δ_bnd ≫ oI_bnd ≫ πV' := by
      rw [← Category.assoc, h_δ_oI]
    -- to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV'
    have h_to_Z_comp : to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV' := by
      change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
        (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
      simp only [Category.assoc, imageSubobject_arrow_comp]
      rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
        (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm, h_ltk_spec]
    -- B_{n+1} is in oI_bnd ≫ πV' terms; we need to show to_Z_n_t factors through
    -- ofLE(B_{n+1}, Z_n) (as a map of subobjects of Z_n.underlying).
    -- Equivalently: B_{n+1}.Factors(to_Z_n_t ≫ Z_n_t.arrow), which we know:
    have h_bnd_fac_to_Z : B_n1_t.Factors (to_Z_n_t ≫ Z_n_t.arrow) := by
      rw [h_to_Z_comp, h_lift_πV']
      apply Subobject.factors_of_factors_right
      change (imageSubobject (oI_bnd ≫ πV')).Factors (oI_bnd ≫ πV')
      rw [Subobject.mk_factors_iff]
      exact ⟨factorThruImage _, by simp⟩
    -- Factor to_Z_n_t through ofLE(B_{n+1}, Z_n)
    have hB_le_Z_n1 : B_n1_t ≤ Z_n_t := by
      change FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1) ≤
        FC.cycleSubobject (s + ↑n) (k - 1) ↑n
      exact le_trans (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑(n + 1))
        (FC.cycleSubobject_antitone (s + ↑n) (k - 1)
          (WithTop.coe_le_coe.mpr (Nat.le_succ n)))
    set factorγ := B_n1_t.factorThru _ h_bnd_fac_to_Z with hfactorγ_def
    have hfactorγ_spec : factorγ ≫ B_n1_t.arrow = to_Z_n_t ≫ Z_n_t.arrow :=
      Subobject.factorThru_arrow _ _ _
    have h_to_Z_eq : to_Z_n_t = factorγ ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 := by
      apply (inferInstance : Mono Z_n_t.arrow).right_cancellation
      simp only [Category.assoc, Subobject.ofLE_arrow, hfactorγ_spec]; rfl
    -- Now ψ = to_Z_n_t ≫ FC.pageπ (s + ↑n) (k - 1) ↑n = factorγ ≫ ofLE(B_{n+1}, Z_n) ≫ FC.pageπ (s + ↑n) (k - 1) ↑n
    change imageSubobject ψ ≤ imageSubobject (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫
      FC.pageπ (s + ↑n) (k - 1) ↑n)
    rw [hψ_def, h_to_Z_eq]
    calc
      imageSubobject ((factorγ ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1) ≫
          FC.pageπ (s + ↑n) (k - 1) ↑n) =
          imageSubobject (factorγ ≫ (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫
            FC.pageπ (s + ↑n) (k - 1) ↑n)) := by
        congr 1
        exact Category.assoc _ _ _
      _ ≤ imageSubobject (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫
          FC.pageπ (s + ↑n) (k - 1) ↑n) := imageSubobject_comp_le _ _
  -- === (≥) direction: imageSubobject(ofLE(B_{n+1}, Z_n) ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) ≤ imageSubobject(ψ) ===
  · -- Strategy: Define σ_bnd (lifting of oI_bnd through kerZ'), cancel factorB (epi),
    -- use pullback to construct w : PB → kerZ with pb_snd ≫ σ_bnd = w ≫ lift_to_kerZ',
    -- then conclude via imageSubobject_epi_comp'_local and imageSubobject_comp_le.
    -- === Step 0: Reconstruct shared definitions from (≤) direction ===
    set imgD_bnd := imageSubobject ((FC.filtration.F (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫
      FC.dToK (k - 1)) with himgD_bnd_def
    set I_bnd := imgD_bnd ⊓ FC.filtration.F (s + ↑n) (k - 1) with hI_bnd_def
    set oI_bnd := Subobject.ofLE I_bnd (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right
      with hoI_bnd_def
    let B_n1_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1)
    let Z_n_t := FC.cycleSubobject (s + ↑n) (k - 1) ↑n
    have hB_le_Z_n1 : B_n1_t ≤ Z_n_t := by
      change FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1) ≤
        FC.cycleSubobject (s + ↑n) (k - 1) ↑n
      exact le_trans (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑(n + 1))
        (FC.cycleSubobject_antitone (s + ↑n) (k - 1)
          (WithTop.coe_le_coe.mpr (Nat.le_succ n)))
    -- === Step 1: Define σ_bnd : I_bnd → kerZ' (lifting oI_bnd through kerZ') ===
    -- oI_bnd ≫ f_n' = 0 because d² = 0 on the image of d.
    have h_oI_fn' : oI_bnd ≫ f_n' = 0 := by
      rw [hf_n'_def]
      rw [show oI_bnd ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
        cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) =
        (oI_bnd ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
        cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) from by
        simp only [Category.assoc]]
      rw [show oI_bnd ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow = I_bnd.arrow
        from Subobject.ofLE_arrow inf_le_right]
      rw [show I_bnd.arrow = Subobject.ofLE I_bnd imgD_bnd inf_le_left ≫ imgD_bnd.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      simp only [Category.assoc]
      have h_imgD_arrow_d : imgD_bnd.arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) = 0 := by
        have hfactor : factorThruImageSubobject
            ((FC.filtration.F (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) ≫
            imgD_bnd.arrow =
            (FC.filtration.F (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1) :=
          imageSubobject_arrow_comp _
        rw [← cancel_epi (factorThruImageSubobject
            ((FC.filtration.F (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)))]
        rw [comp_zero, ← Category.assoc, hfactor, Category.assoc,
          FC.dToK_comp_d, comp_zero]
      rw [show Subobject.ofLE I_bnd imgD_bnd inf_le_left ≫ imgD_bnd.arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
        cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) =
        (Subobject.ofLE I_bnd imgD_bnd inf_le_left ≫ (imgD_bnd.arrow ≫ FC.complex.d (k - 1) (k - 1 - 1))) ≫
        cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) from by
        simp only [Category.assoc]]
      rw [h_imgD_arrow_d, comp_zero, zero_comp]
    set σ_bnd := factorThruKernelSubobject f_n' oI_bnd h_oI_fn' with hσ_bnd_def
    have hσ_bnd_spec : σ_bnd ≫ kerZ'.arrow = oI_bnd :=
      factorThruKernelSubobject_comp_arrow f_n' oI_bnd h_oI_fn'
    -- === Step 2: Cancel factorB (epi) ===
    set factorB := factorThruImageSubobject (oI_bnd ≫ πV') with hfactorB_def
    haveI hfactorB_epi : Epi factorB := inferInstance
    -- Rewrite the theorem target to the local boundary/cycle aliases.
    change imageSubobject (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫
      FC.pageπ (s + ↑n) (k - 1) ↑n) ≤ imageSubobject ψ
    have h_factorB_ofLE : factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫
        Z_n_t.arrow = oI_bnd ≫ πV' := by
      calc
        factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ Z_n_t.arrow =
            factorB ≫ B_n1_t.arrow := by
              exact congrArg (fun q => factorB ≫ q)
                (Subobject.ofLE_arrow hB_le_Z_n1)
        _ = oI_bnd ≫ πV' := imageSubobject_arrow_comp (oI_bnd ≫ πV')
    -- === Step 3: Show factorB ≫ ofLE = σ_to_Z via mono cancellation ===
    set σ_to_Z := σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') with hσ_to_Z_def
    have hσ_to_Z_spec : σ_to_Z ≫ Z_n_t.arrow = oI_bnd ≫ πV' := by
      change (σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
        (imageSubobject (kerZ'.arrow ≫ πV')).arrow = oI_bnd ≫ πV'
      simp only [Category.assoc, imageSubobject_arrow_comp]
      rw [show σ_bnd ≫ kerZ'.arrow ≫ πV' = (σ_bnd ≫ kerZ'.arrow) ≫ πV'
        from (Category.assoc _ _ _).symm, hσ_bnd_spec]
    have h_factorB_ofLE_eq : factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 = σ_to_Z := by
      apply (inferInstance : Mono Z_n_t.arrow).right_cancellation
      calc
        (factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1) ≫ Z_n_t.arrow =
            oI_bnd ≫ πV' := by
              simpa only [← Category.assoc] using h_factorB_ofLE
        _ = σ_to_Z ≫ Z_n_t.arrow := hσ_to_Z_spec.symm
    -- Goal (after show): imageSubobject(ofLE(B_n1_t, Z_n_t) ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) ≤ imageSubobject(ψ)
    -- Rewrite factorB out:
    -- imageSubobject(factorB ≫ ofLE ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) = imageSubobject(ofLE ≫ FC.pageπ (s + ↑n) (k - 1) ↑n)
    -- Then factorB ≫ ofLE = σ_to_Z = σ_bnd ≫ q,
    -- and ψ = to_Z_n_t ≫ FC.pageπ (s + ↑n) (k - 1) ↑n = lift_to_kerZ' ≫ q ≫ FC.pageπ (s + ↑n) (k - 1) ↑n
    -- Use have + calc to avoid rewrite issues with opaque names
    have h_img_ofLE_eq : imageSubobject (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) =
        imageSubobject (σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) := by
      erw [← imageSubobject_epi_comp'_local factorB
        (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ FC.pageπ (s + ↑n) (k - 1) ↑n)]
      congr 1
      calc
        factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ FC.pageπ (s + ↑n) (k - 1) ↑n =
            (factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1) ≫ FC.pageπ (s + ↑n) (k - 1) ↑n :=
              (Category.assoc _ _ _).symm
        _ = σ_to_Z ≫ FC.pageπ (s + ↑n) (k - 1) ↑n := by rw [h_factorB_ofLE_eq]; rfl
        _ = (σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
            FC.pageπ (s + ↑n) (k - 1) ↑n := by rw [hσ_to_Z_def]
        _ = σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫
            FC.pageπ (s + ↑n) (k - 1) ↑n := Category.assoc _ _ _
    rw [h_img_ofLE_eq]
    -- Goal: imageSubobject(σ_bnd ≫ q ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) ≤ imageSubobject(ψ)
    suffices h_le :
        imageSubobject (σ_bnd ≫
          factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) ≤
        imageSubobject (lift_to_kerZ' ≫
          factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) by
      calc imageSubobject (σ_bnd ≫
              factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n)
          ≤ imageSubobject (lift_to_kerZ' ≫
              factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫
                FC.pageπ (s + ↑n) (k - 1) ↑n) := h_le
        _ = imageSubobject ψ := by rw [hψ_def, hto_Z_n_t_def, Category.assoc]
    -- Goal: imageSubobject(σ_bnd ≫ q ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) ≤ imageSubobject(lift_to_kerZ' ≫ q ≫ FC.pageπ (s + ↑n) (k - 1) ↑n)
    -- where q = factorThruImageSubobject(kerZ'.arrow ≫ πV')
    -- === Step 4: Pullback of factorD (epi) against oI_to_imgD ===
    have h_idx_eq_s' : (s : ℤ) + ↑n - ↑(n + 1) + 1 = s := by push_cast; omega
    set imgD_src := (FC.filtration.F (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫
      FC.dToK (k - 1) with himgD_src_def
    set factorD := factorThruImageSubobject imgD_src with hfactorD_def
    haveI hfactorD_epi : Epi factorD := inferInstance
    have hfactorD_spec : factorD ≫ imgD_bnd.arrow = imgD_src :=
      imageSubobject_arrow_comp imgD_src
    set oI_to_imgD := Subobject.ofLE I_bnd imgD_bnd inf_le_left with hoI_to_imgD_def
    set pb_fst := Limits.pullback.fst factorD oI_to_imgD
    set pb_snd := Limits.pullback.snd factorD oI_to_imgD
    have hpb_cond : pb_fst ≫ factorD = pb_snd ≫ oI_to_imgD := Limits.pullback.condition
    haveI : Epi pb_snd := Abelian.epi_pullback_of_epi_f factorD oI_to_imgD
    -- === Step 5: Transport eqH and prove eqH ≫ fil(s)(k).arrow ≫ d(k) = imgD_src ===
    set eqH := eqToHom (show Subobject.underlying.obj
        (FC.filtration.F (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)) =
        Subobject.underlying.obj (FC.filtration.F s k) from by
      rw [h_idx_eq_s', show (k - 1 : ℤ) + 1 = k from by omega]) with heqH_def
    have h_eqH_d : eqH ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) = imgD_src := by
      conv_lhs => rw [← eqToHom_arrow_dToK_local FC s k]
      rw [heqH_def]; simp only [← Category.assoc]; rw [eqToHom_trans]
      rw [himgD_src_def]; congr 1
      exact (Subobject.arrow_congr _ _ (by congr 1))
    -- pb_fst ≫ imgD_src = pb_snd ≫ I_bnd.arrow
    have h_pb_imgD : pb_fst ≫ imgD_src = pb_snd ≫ I_bnd.arrow := by
      calc pb_fst ≫ imgD_src
          = pb_fst ≫ (factorD ≫ imgD_bnd.arrow) := by rw [imageSubobject_arrow_comp imgD_src]
        _ = (pb_fst ≫ factorD) ≫ imgD_bnd.arrow := by rw [Category.assoc]
        _ = (pb_snd ≫ oI_to_imgD) ≫ imgD_bnd.arrow := by rw [hpb_cond]
        _ = pb_snd ≫ (oI_to_imgD ≫ imgD_bnd.arrow) := by simp only [Category.assoc]
        _ = pb_snd ≫ I_bnd.arrow := by congr 1; exact Subobject.ofLE_arrow inf_le_left
    -- === Step 6: (pb_fst ≫ eqH) ≫ f_n = 0 ===
    have h_pb_fn : (pb_fst ≫ eqH) ≫ f_n = 0 := by
      rw [hf_n_def]; simp only [Category.assoc]
      rw [show pb_fst ≫ eqH ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
        cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) =
        (pb_fst ≫ (eqH ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))) ≫
        cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) from by simp only [Category.assoc]]
      rw [h_eqH_d]
      -- Goal: (pb_fst ≫ imgD_src) ≫ cokernel.π(fil(s+n)(k-1).arrow) = 0
      rw [h_pb_imgD]
      -- Goal: (pb_snd ≫ I_bnd.arrow) ≫ cokernel.π(fil(s+n)(k-1).arrow) = 0
      simp only [Category.assoc]
      rw [show I_bnd.arrow = oI_bnd ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow
        from (Subobject.ofLE_arrow inf_le_right).symm]
      simp only [Category.assoc]
      rw [cokernel.condition, comp_zero, comp_zero]
    -- === Step 7: Factor through kerZ ===
    set w := factorThruKernelSubobject f_n (pb_fst ≫ eqH) h_pb_fn with hw_def
    have hw_spec : w ≫ kerZ.arrow = pb_fst ≫ eqH :=
      factorThruKernelSubobject_comp_arrow f_n (pb_fst ≫ eqH) h_pb_fn
    -- === Step 8: pb_snd ≫ σ_bnd = w ≫ lift_to_kerZ' (mono cancellation on kerZ'.arrow) ===
    have h_pb_snd_σ_eq : pb_snd ≫ σ_bnd = w ≫ lift_to_kerZ' := by
      apply (inferInstance : Mono kerZ'.arrow).right_cancellation
      rw [Category.assoc, hσ_bnd_spec, Category.assoc, h_ltk_spec]
      -- Goal: pb_snd ≫ oI_bnd = w ≫ lift_n
      -- Both sides map to fil(s+n)(k-1).underlying. Use mono cancellation on fil(s+n)(k-1).arrow.
      apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
      simp only [Category.assoc]
      rw [h_lift_spec, ← Category.assoc w kerZ.arrow, hw_spec,
        Category.assoc, h_eqH_d, h_pb_imgD]
      -- LHS: pb_snd ≫ oI_bnd ≫ fil(s+n)(k-1).arrow  RHS: pb_snd ≫ I_bnd.arrow
      congr 1; exact Subobject.ofLE_arrow inf_le_right
    -- === Step 9: Conclude ===
    rw [← imageSubobject_epi_comp'_local pb_snd
      (σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n)]
    rw [show pb_snd ≫ σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n =
      (pb_snd ≫ σ_bnd) ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n from by
      simp only [Category.assoc]]
    rw [h_pb_snd_σ_eq]
    simp only [Category.assoc]
    exact imageSubobject_comp_le _ _

end KIP126.Core.SpectralSequence.FilteredComplex
