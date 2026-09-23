import KIP126.Def.SpectralSequence.FilteredPage.Data

/-!
# Differential on quotient pages

The differential is induced by the canonical filtered chain complex, by lifting
through the cycle kernel and descending through its image and the boundary
quotient. This adapts the completed construction in
`KIPBase/SpectralSequence/FilteredComplex.lean` at `dc4a7d1`.
Finite-page construction does not require boundedness of the filtration.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem fil_arrow_eqToHom (FC : FilteredComplex C)
    (s : ℤ) (a b : ℤ) (h : a = b) :
    eqToHom (show Subobject.underlying.obj (FC.filtration.F s a) =
      Subobject.underlying.obj (FC.filtration.F s b) from by subst h; rfl) ≫
    (FC.filtration.F s b).arrow = (FC.filtration.F s a).arrow ≫
    eqToHom (show FC.complex.X a = FC.complex.X b from by subst h; rfl) := by
  subst h; simp

/-- Transport lemma for the differential along an integer equality:
    `eqToHom ≫ FC.complex.d b (b - 1) = FC.complex.d a (a - 1) ≫ eqToHom`. -/
private theorem d_eqToHom' (FC : FilteredComplex C)
    (a b : ℤ) (h : a = b) :
    eqToHom (show FC.complex.X a = FC.complex.X b from by subst h; rfl) ≫
    FC.complex.d b (b - 1) = FC.complex.d a (a - 1) ≫
    eqToHom (show FC.complex.X (a - 1) = FC.complex.X (b - 1) from by subst h; rfl) := by
  subst h; simp

/-- `eqToHom ≫ dToK(k-1) = d(k)`: the transported differential composed with eqToHom
    gives the original differential. (Generalized version with free variables.) -/
private theorem eqToHom_arrow_dToK_gen (FC : FilteredComplex C)
    (s : ℤ) (m k : ℤ) (hmk : m + 1 = k) :
    eqToHom (show Subobject.underlying.obj (FC.filtration.F s k) =
      Subobject.underlying.obj (FC.filtration.F s (m + 1)) by rw [hmk]) ≫
    ((FC.filtration.F s (m + 1)).arrow ≫ FC.dToK m) =
      (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      eqToHom (congr_arg FC.complex.X (show k - 1 = m by omega)) := by
  subst hmk
  simp [FilteredComplex.dToK]

/-- Specialized transport: `eqToHom ≫ F^s((k-1)+1).arrow ≫ dToK(k-1) = F^s(k).arrow ≫ d(k)`. -/
private theorem eqToHom_arrow_dToK (FC : FilteredComplex C)
    (s k : ℤ) :
    eqToHom (show Subobject.underlying.obj (FC.filtration.F s k) =
      Subobject.underlying.obj (FC.filtration.F s ((k - 1) + 1)) by
      rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
    ((FC.filtration.F s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
      (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
  rw [FC.eqToHom_arrow_dToK_gen s (k - 1) k (by omega)]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The induced differential on pages: `d_r : E_r^{s,k} → E_r^{s+r,k-1}`.
    This maps Z_r-cycles modulo B_r-boundaries at (s,k) to the same at (s+r,k-1),
    using the original differential d of the filtered complex.

    For `r = n : ℕ`:
    - Source: `E_n^{s,k} = Z_n^{s,k} / B_n^{s,k}` where
      `Z_n = { x ∈ F^s | dx ∈ F^{s+n} }` and `B_n = { dz | z ∈ F^{s-n+1}, dz ∈ F^s }`
    - Target: `E_n^{s+n,k-1} = Z_n^{s+n,k-1} / B_n^{s+n,k-1}`
    - Map: send class of x to class of dx -/
noncomputable def pageDifferential (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    FC.pageObj s k ↑n ⟶ FC.pageObj (s + ↑n) (k - 1) ↑n := by
  set ι_s := Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k) with hι_s_def
  let πV := FC.filtration.toAssociatedGraded s k
  let f_n := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
  let kerZ := kernelSubobject f_n
  set ι_t := Subobject.ofLE (FC.filtration.F (s + ↑n + 1) (k - 1)) (FC.filtration.F (s + ↑n) (k - 1))
    (FC.filtration.decreasing (s + ↑n) (k - 1)) with hι_t_def
  let πV' := FC.filtration.toAssociatedGraded (s + ↑n) (k - 1)
  let f_n' := (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow)
  let kerZ' := kernelSubobject f_n'
  -- === Step 1: Lift d-image through F^{s+n}(k-1) ===
  have h_ker_fn : kerZ.arrow ≫ f_n = 0 := kernelSubobject_arrow_comp f_n
  have h_factor_zero : (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc] at h_ker_fn ⊢; exact h_ker_fn
  set lift_n := Abelian.monoLift (FC.filtration.F (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))
    h_factor_zero with hlift_n_def
  have h_lift_spec : lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
      kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) :=
    Abelian.monoLift_comp _ _ _
  -- === Step 2: Show lift_n factors through kerZ' (using d²=0) ===
  have h_lift_in_kerZ' : lift_n ≫ f_n' = 0 := by
    calc lift_n ≫ f_n'
        = lift_n ≫ ((FC.filtration.F (s + ↑n) (k - 1)).arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
            cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow)) := rfl
      _ = ((lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫ FC.complex.d (k - 1) (k - 1 - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          simp only [Category.assoc]
      _ = ((kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫ FC.complex.d (k - 1) (k - 1 - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          rw [h_lift_spec]
      _ = (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ (FC.complex.d k (k - 1) ≫ FC.complex.d (k - 1) (k - 1 - 1))) ≫
            cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          simp only [Category.assoc]
      _ = 0 := by rw [FC.complex.d_comp_d k]; simp only [comp_zero, zero_comp]
  set lift_to_kerZ' := factorThruKernelSubobject f_n' lift_n h_lift_in_kerZ'
    with hlift_to_kerZ'_def
  -- === Step 3: Build ψ : kerZ.underlying → target page ===
  set to_Z_n_t := lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')
    with hto_Z_n_t_def
  set pageπ' := FC.pageπ (s + ↑n) (k - 1) ↑n with hpageπ'_def
  set ψ := to_Z_n_t ≫ pageπ' with hψ_def
  -- === Step 4: Descend ψ through epi (kerZ → Z_n_s) using Abelian.epiDesc ===
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV) with hp_def
  haveI : Epi p := inferInstance
  have h_ker_p_ψ : kernel.ι p ≫ ψ = 0 := by
    -- === Step B: lift_n spec ===
    have h_comp_eq : kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
        kernel.ι p ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
      simp only [h_lift_spec]
    -- === Step C: Factor through imgD ⊓ F^{s+n}(k-1) ===
    set imgD := imageSubobject ((FC.filtration.F (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1))
      with himgD_def
    have h_fac_imgD : imgD.Factors
        (kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
      rw [h_comp_eq]
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
      set α := Abelian.monoLift ι_s (kernel.ι p ≫ kerZ.arrow) h1' with hα_def
      have hα_spec : α ≫ ι_s = kernel.ι p ≫ kerZ.arrow := Abelian.monoLift_comp _ _ _
      have h_ι_arrow : ι_s ≫ (FC.filtration.F s k).arrow = (FC.filtration.F (s + 1) k).arrow := by
        exact Subobject.ofLE_arrow (FC.filtration.decreasing s k)
      have h_rewrite : kernel.ι p ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
          α ≫ ((FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1)) := by
        conv_lhs => rw [show kernel.ι p ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
          ((kernel.ι p ≫ kerZ.arrow) ≫ (FC.filtration.F s k).arrow) ≫ FC.complex.d k (k - 1) from by
          simp only [Category.assoc]]
        rw [← hα_spec, show (α ≫ ι_s) ≫ (FC.filtration.F s k).arrow = α ≫ (ι_s ≫ (FC.filtration.F s k).arrow) from
          Category.assoc _ _ _, h_ι_arrow, Category.assoc]
      rw [h_rewrite]
      apply Subobject.factors_of_factors_right
      have h_transport : eqToHom (show Subobject.underlying.obj (FC.filtration.F (s + 1) k) =
          Subobject.underlying.obj (FC.filtration.F (s + 1) ((k - 1) + 1)) by
          rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
          ((FC.filtration.F (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
          (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) :=
        FC.eqToHom_arrow_dToK (s + 1) k
      rw [← h_transport, himgD_def, Subobject.mk_factors_iff]
      exact ⟨eqToHom (by rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
        factorThruImage ((FC.filtration.F (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)), by simp⟩
    have h_fac_fil : (FC.filtration.F (s + ↑n) (k - 1)).Factors
        (kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) :=
      Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow lift_n)
    set I := imgD ⊓ FC.filtration.F (s + ↑n) (k - 1) with hI_def
    have h_fac_I : I.Factors (kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) :=
      (Subobject.inf_factors _).mpr ⟨h_fac_imgD, h_fac_fil⟩
    set δ := I.factorThru _ h_fac_I with hδ_def
    have hδ_spec : δ ≫ I.arrow = kernel.ι p ≫ lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow :=
      Subobject.factorThru_arrow _ _ _
    -- === Step D: δ ≫ ofLE(I, F^{s+n}) = kernel.ι p ≫ lift_n ===
    have h_δ_ofLE : δ ≫ Subobject.ofLE I (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right =
        kernel.ι p ≫ lift_n := by
      apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
      rw [Category.assoc, Subobject.ofLE_arrow, hδ_spec]
      simp only [Category.assoc]
    -- === Step E: Match boundary definition with I ===
    have h_imgD_bnd : imageSubobject ((FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) = imgD := by
      rw [show (s : ℤ) + (↑n : ℤ) - (↑n : ℤ) + 1 = s + 1 from by omega]
    have h_I_bnd : imageSubobject ((FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) ⊓ FC.filtration.F (s + ↑n) (k - 1) = I := by
      rw [h_imgD_bnd]


    -- === Step F: Show B_n_t.Factors (kernel.ι p ≫ lift_n ≫ πV') ===

    have h_bnd_fac : (FC.boundarySubobject (s + ↑n) (k - 1) ↑n).Factors
        (kernel.ι p ≫ lift_n ≫ πV') := by
      rw [show kernel.ι p ≫ lift_n ≫ πV' = (kernel.ι p ≫ lift_n) ≫ πV'
        from (Category.assoc _ _ _).symm,
        ← h_δ_ofLE, Category.assoc]
      apply Subobject.factors_of_factors_right
      set I_bnd := imageSubobject ((FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) ⊓ FC.filtration.F (s + ↑n) (k - 1) with hI_bnd_def
      have h_I_le_Ibnd : I ≤ I_bnd := le_of_eq h_I_bnd.symm
      have h_ofLE_factor : Subobject.ofLE I (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right =
          Subobject.ofLE I I_bnd h_I_le_Ibnd ≫
          Subobject.ofLE I_bnd (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right := by
        apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
        simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [h_ofLE_factor, Category.assoc]
      apply Subobject.factors_of_factors_right
      change (imageSubobject
        (Subobject.ofLE I_bnd (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right ≫ πV')).Factors
        (Subobject.ofLE I_bnd (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right ≫ πV')
      rw [Subobject.mk_factors_iff]
      exact ⟨factorThruImage _, by simp⟩
    -- === Step G: Show kernel.ι p ≫ ψ = 0 ===
    set B_n_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑n with hB_n_t_def
    let Z_n_t := FC.cycleSubobject (s + ↑n) (k - 1) ↑n
    have hZ_n_t_def : Z_n_t = FC.cycleSubobject (s + ↑n) (k - 1) ↑n := rfl
    have hB_le_Z := FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n
    have h_to_Z_comp : to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV' := by
      change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
        (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
      simp only [Category.assoc, imageSubobject_arrow_comp]
      rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
        (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm]
      rw [show lift_to_kerZ' ≫ kerZ'.arrow = lift_n from by
        rw [hlift_to_kerZ'_def]
        exact factorThruKernelSubobject_comp_arrow f_n' lift_n h_lift_in_kerZ']
    have h_ker_to_Z_fac : B_n_t.Factors (kernel.ι p ≫ to_Z_n_t ≫ Z_n_t.arrow) := by
      rw [h_to_Z_comp]
      exact h_bnd_fac
    set γ := B_n_t.factorThru _ h_ker_to_Z_fac with hγ_def
    have hγ_spec : γ ≫ B_n_t.arrow = kernel.ι p ≫ to_Z_n_t ≫ Z_n_t.arrow :=
      Subobject.factorThru_arrow _ _ _
    have h_factor_B : kernel.ι p ≫ to_Z_n_t =
        γ ≫ Subobject.ofLE B_n_t Z_n_t hB_le_Z := by
      apply (inferInstance : Mono Z_n_t.arrow).right_cancellation
      calc
        (kernel.ι p ≫ to_Z_n_t) ≫ Z_n_t.arrow =
            kernel.ι p ≫ to_Z_n_t ≫ Z_n_t.arrow := Category.assoc _ _ _
        _ = γ ≫ B_n_t.arrow := hγ_spec.symm
        _ = (γ ≫ Subobject.ofLE B_n_t Z_n_t hB_le_Z) ≫ Z_n_t.arrow := by
          rw [Category.assoc, Subobject.ofLE_arrow]
    have h_cok : Subobject.ofLE B_n_t Z_n_t hB_le_Z ≫ pageπ' = 0 := by
      rw [show pageπ' = FC.pageπ (s + ↑n) (k - 1) ↑n from rfl]
      change Subobject.ofLE B_n_t Z_n_t hB_le_Z ≫
        cokernel.π (Subobject.ofLE (FC.boundarySubobject (s + ↑n) (k - 1) ↑n)
          (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)
          (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n)) = 0
      exact cokernel.condition _
    rw [hψ_def]
    calc kernel.ι p ≫ to_Z_n_t ≫ pageπ'
        = (kernel.ι p ≫ to_Z_n_t) ≫ pageπ' := (Category.assoc _ _ _).symm
      _ = (γ ≫ Subobject.ofLE B_n_t Z_n_t hB_le_Z) ≫ pageπ' := by
        rw [← h_factor_B]
      _ = γ ≫ (Subobject.ofLE B_n_t Z_n_t hB_le_Z ≫ pageπ') := Category.assoc _ _ _
      _ = γ ≫ 0 := by rw [h_cok]
      _ = 0 := comp_zero
  set h_on_Zn := Abelian.epiDesc p ψ h_ker_p_ψ with hh_on_Zn_def
  -- === Step 5: Descend through source page cokernel ===
  have h_B_zero : Subobject.ofLE (FC.boundarySubobject s k ↑n)
      (FC.cycleSubobject s k ↑n)
      (FC.B_le_Z_aux s k ↑n) ≫ h_on_Zn = 0 := by
    let imgD_s := imageSubobject ((FC.filtration.F (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k)
    let I_s := imgD_s ⊓ FC.filtration.F s k
    let oI_s := Subobject.ofLE I_s (FC.filtration.F s k) inf_le_right
    have h_B_eq : FC.boundarySubobject s k ↑n = imageSubobject (oI_s ≫ πV) := by
      simp [FilteredComplex.boundarySubobject, imgD_s, I_s, oI_s, πV]
    have h_Z_eq : FC.cycleSubobject s k ↑n = imageSubobject (kerZ.arrow ≫ πV) := by
      simp [FilteredComplex.cycleSubobject, kerZ, f_n, πV]
    -- === Step 1: oI_s ≫ f_n = 0 (boundary elements satisfy the cycle condition) ===
    have h_zero_s : oI_s ≫ f_n = 0 := by
      change Subobject.ofLE I_s (FC.filtration.F s k) inf_le_right ≫
        ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
          cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)) = 0
      simp only [← Category.assoc]
      rw [Subobject.ofLE_arrow]
      rw [show I_s.arrow =
          Subobject.ofLE I_s imgD_s inf_le_left ≫ imgD_s.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      simp only [Category.assoc]
      have hd : imgD_s.arrow ≫ FC.complex.d k (k - 1) = 0 := by
        rw [← cancel_epi (factorThruImageSubobject
          ((FC.filtration.F (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k))]
        rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp,
          Category.assoc, FC.dToK_comp_d, comp_zero]
      rw [show imgD_s.arrow ≫ FC.complex.d k (k - 1) ≫ cokernel.π _ =
        (imgD_s.arrow ≫ FC.complex.d k (k - 1)) ≫ cokernel.π _
        from (Category.assoc _ _ _).symm,
        hd, zero_comp, comp_zero]
    -- === Step 2: Lift oI_s to kerZ ===
    set σ_s := factorThruKernelSubobject f_n oI_s h_zero_s with hσ_s_def
    have hσ_s_spec : σ_s ≫ kerZ.arrow = oI_s :=
      factorThruKernelSubobject_comp_arrow f_n oI_s h_zero_s
    -- === Step 3: σ_s ≫ p ≫ Z_n.arrow = oI_s ≫ πV ===
    have hp_spec : p ≫ (FC.cycleSubobject s k ↑n).arrow = kerZ.arrow ≫ πV := by
      change factorThruImageSubobject (kerZ.arrow ≫ πV) ≫
        (imageSubobject (kerZ.arrow ≫ πV)).arrow = kerZ.arrow ≫ πV
      exact imageSubobject_arrow_comp (kerZ.arrow ≫ πV)
    -- === Step 4: Cancel epi to reduce to σ_s ≫ ψ = 0 ===
    set q := factorThruImageSubobject (oI_s ≫ πV) ≫
      eqToHom (congrArg (fun X : Subobject (FC.filtration.associatedGraded s k) =>
        Subobject.underlying.obj X) h_B_eq.symm) with hq_def
    haveI : Epi q := inferInstance
    have hq_arrow : q ≫ (FC.boundarySubobject s k ↑n).arrow = oI_s ≫ πV := by
      rw [hq_def, Category.assoc,
        Subobject.arrow_congr (imageSubobject (oI_s ≫ πV))
          (FC.boundarySubobject s k ↑n) h_B_eq.symm]
      exact imageSubobject_arrow_comp (oI_s ≫ πV)
    have hq_ofLE_spec : q ≫ Subobject.ofLE (FC.boundarySubobject s k ↑n)
        (FC.cycleSubobject s k ↑n) (FC.B_le_Z_aux s k ↑n) ≫
        (FC.cycleSubobject s k ↑n).arrow = oI_s ≫ πV := by
      simp only [Subobject.ofLE_arrow]
      exact hq_arrow
    have hσ_p_spec : σ_s ≫ p ≫ (FC.cycleSubobject s k ↑n).arrow = oI_s ≫ πV := by
      simp only [hp_spec]
      rw [show σ_s ≫ kerZ.arrow ≫ πV = (σ_s ≫ kerZ.arrow) ≫ πV from by
        simp only [Category.assoc]]
      rw [hσ_s_spec]
    have hσ_factor : q ≫ Subobject.ofLE (FC.boundarySubobject s k ↑n)
        (FC.cycleSubobject s k ↑n) (FC.B_le_Z_aux s k ↑n) = σ_s ≫ p := by
      apply (inferInstance : Mono (FC.cycleSubobject s k ↑n).arrow).right_cancellation
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [Category.assoc, hσ_p_spec]
      simpa only [hq_def, Category.assoc] using hq_arrow
    -- === Step 5: σ_s ≫ lift_n = 0 (key: d² = 0) ===
    have hσ_lift_zero : σ_s ≫ lift_n = 0 := by
      apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
      rw [zero_comp]
      simp only [Category.assoc]
      rw [h_lift_spec]
      rw [show σ_s ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
        (σ_s ≫ kerZ.arrow) ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) from by
        simp only [Category.assoc]]
      rw [hσ_s_spec]
      rw [show oI_s ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) =
        (oI_s ≫ (FC.filtration.F s k).arrow) ≫ FC.complex.d k (k - 1) from by simp only [Category.assoc]]
      rw [show oI_s ≫ (FC.filtration.F s k).arrow = I_s.arrow from Subobject.ofLE_arrow inf_le_right]
      rw [show I_s.arrow =
          Subobject.ofLE I_s imgD_s inf_le_left ≫ imgD_s.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc]
      have hd : imgD_s.arrow ≫ FC.complex.d k (k - 1) = 0 := by
        rw [← cancel_epi (factorThruImageSubobject
          ((FC.filtration.F (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k))]
        rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp,
          Category.assoc, FC.dToK_comp_d, comp_zero]
      rw [hd, comp_zero]
    -- === Step 6: σ_s ≫ ψ = 0 ===
    have hσ_ψ_zero : σ_s ≫ ψ = 0 := by
      rw [hψ_def, hto_Z_n_t_def, show σ_s ≫ (lift_to_kerZ' ≫
          factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫ pageπ' =
        ((σ_s ≫ lift_to_kerZ') ≫
          factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫ pageπ'
        from by simp only [Category.assoc]]
      have h_σ_lift_kerZ' : σ_s ≫ lift_to_kerZ' = 0 := by
        apply (inferInstance : Mono kerZ'.arrow).right_cancellation
        rw [zero_comp]
        simp only [Category.assoc]
        rw [hlift_to_kerZ'_def, factorThruKernelSubobject_comp_arrow]
        exact hσ_lift_zero
      rw [h_σ_lift_kerZ', zero_comp, zero_comp]
    -- === Step 7: Cancel epi q to conclude ===
    have h_comp_zero : q ≫ (Subobject.ofLE (FC.boundarySubobject s k ↑n)
        (FC.cycleSubobject s k ↑n)
        (FC.B_le_Z_aux s k ↑n) ≫ h_on_Zn) = 0 := by
      rw [← Category.assoc, hσ_factor, Category.assoc, hh_on_Zn_def,
        Abelian.comp_epiDesc]
      exact hσ_ψ_zero
    exact (cancel_epi q).mp (by rw [h_comp_zero, comp_zero])
  exact cokernel.desc _ h_on_Zn h_B_zero



end KIP126.Core.SpectralSequence.FilteredComplex
