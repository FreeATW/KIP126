import KIP126.Def.SpectralSequence.FilteredComplex.SpectralSequenceConstruction.Data
import KIP126.Def.SpectralSequence.FilteredComplex.HomologyTarget.Data
import KIP126.Def.SpectralSequence.Convergence.SSData.Proofs

/-!
# Weak convergence of the filtered-complex spectral sequence

This is the axiom-free migration of the completed weak-convergence construction
from KIPBase.  The target filtration is the explicit bridge from KIP126's
canonical algebra filtration to the nested-subobject spectral-sequence API.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

set_option linter.dupNamespace false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def FilteredComplex.weakConvergence (FC : FilteredComplex C)
    (bnd : FC.IsBounded) :
    Convergence (FC.toSpectralSequence bnd) FC.homologySSObj FC.homologySSFiltration where
  -- The natural reindexing: (s, k) ↦ (s, k) (identity on bidegrees)
  reindex := fun k => k
  reindex_bijective := Function.bijective_id
  -- The infinity page is identified with the associated graded of the
  -- historical homology filtration by explicit mutually inverse maps.
  iso := fun ⟨s, k⟩ => by
    change (FC.toSSData bnd s k).eInfty ≅ FC.homologySSFiltration.associatedGraded s k
    unfold SSData.eInfty SSData.page Filtration.associatedGraded
    -- Goal: cokernel(ofLE (B⊤) (Z⊤) _) ≅ cokernel(ofLE (F_{s+1}H_k) (F_sH_k) _)
    -- Abbreviations
    let S := ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1)) (FC.d_comp_d (k + 1))
    let e_deg : FC.A k = FC.A (k + 1 - 1) := congr_arg FC.A (show k = k + 1 - 1 by omega)
    let ι_fil := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
    let πV := cokernel.π ι_fil
    let f_Z := (FC.fil s k).arrow ≫ FC.d k
    let kerZ := kernelSubobject f_Z
    -- φ_to_X2 : kerZ.underlying → S.X₂ (= FC.A(k+1-1))
    let φ_to_X2 := kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg
    have h_lift : φ_to_X2 ≫ S.g = 0 := by
      change (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) ≫ S.g = 0
      simp only [Category.assoc]
      have : eqToHom e_deg ≫ S.g =
          FC.d k ≫ eqToHom (congr_arg FC.A (show k - 1 = (k + 1 - 1) - 1 by omega)) := by
        simp [S]
      rw [this, ← Category.assoc, ← Category.assoc,
        show (kerZ.arrow ≫ (FC.fil s k).arrow) ≫ FC.d k = kerZ.arrow ≫ f_Z
          from by simp only [f_Z, Category.assoc],
        kernelSubobject_arrow_comp, zero_comp]
    -- φ_pre : kerZ.underlying → S.homology
    let φ_pre := S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ
    -- I_s for the homologyFiltration
    let I_s := kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1)
    have h_zero_s : I_s.arrow ≫ S.g = 0 := by
      rw [show I_s.arrow = Subobject.ofLE I_s (kernelSubobject S.g)
          inf_le_left ≫ (kernelSubobject S.g).arrow
        from (Subobject.ofLE_arrow inf_le_left).symm,
        Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    let gen_s := S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ
    -- Show φ_to_X2 factors through I_s.arrow, so φ_pre factors through gen_s
    -- This means imageSubobject(φ_pre) ≤ imageSubobject(gen_s) = F_s
    have h_factors_I : I_s.Factors φ_to_X2 := by
      rw [show I_s = kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1) from rfl,
          Subobject.inf_factors φ_to_X2]
      refine ⟨kernelSubobject_factors S.g φ_to_X2 h_lift, ?_⟩
      -- Need: (FC.fil s (k+1-1)).Factors φ_to_X2
      -- φ_to_X2 = kerZ.arrow ≫ (fil s k).arrow ≫ eqToHom(e_deg)
      -- We use: (fil s k).arrow ≫ eqToHom = eqToHom_sub ≫ (fil s (k+1-1)).arrow
      -- so φ_to_X2 = (kerZ.arrow ≫ eqToHom_sub) ≫ (fil s (k+1-1)).arrow
      let e_sub := congr_arg (fun j => Subobject.underlying.obj (FC.fil s j))
          (show k = k + 1 - 1 by omega)
      have h_transport : (FC.fil s k).arrow ≫ eqToHom e_deg = eqToHom e_sub ≫
          (FC.fil s (k + 1 - 1)).arrow := by
        -- Use the Mono property: compose both sides with the identity on A(k+1-1)
        -- and show they agree. Actually, we can use eqToHom_naturality.
        -- eqToHom at object level is functorial, so the naturality square commutes.
        -- For `FC.fil s` applied to equal indices, the arrow commutes with eqToHom.
        -- We prove this by induction on the proof of equality.
        -- Since we can't subst directly, use proof irrelevance + a general lemma.
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil s a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j)) h) ≫
            (FC.fil s b).arrow := by
          intro a b h; subst h; simp
        exact this k (k + 1 - 1) (by omega)
      have h_φ_eq : φ_to_X2 = (kerZ.arrow ≫ eqToHom e_sub) ≫
          (FC.fil s (k + 1 - 1)).arrow := by
        change kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg =
          (kerZ.arrow ≫ eqToHom e_sub) ≫ (FC.fil s (k + 1 - 1)).arrow
        rw [Category.assoc, h_transport, ← Category.assoc]
      rw [h_φ_eq]
      exact Subobject.factors_comp_arrow _
    -- Factor: kerZ → I_s
    let kerZ_to_Is := Subobject.factorThru I_s φ_to_X2 h_factors_I
    -- Key property: kerZ_to_Is ≫ I_s.arrow = φ_to_X2
    have h_kerZ_to_Is : kerZ_to_Is ≫ I_s.arrow = φ_to_X2 :=
      Subobject.factorThru_arrow I_s φ_to_X2 h_factors_I
    -- liftCycles is functorial: kerZ_to_Is ≫ gen_s = φ_pre
    have h_func : kerZ_to_Is ≫ gen_s = φ_pre := by
      change kerZ_to_Is ≫ (S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ) =
        S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ
      rw [← Category.assoc]
      congr 1
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.liftCycles_i, S.liftCycles_i, h_kerZ_to_Is]
    -- imageSubobject(φ_pre) ≤ imageSubobject(gen_s) = F_s
    have h_img_le : imageSubobject φ_pre ≤ imageSubobject gen_s := by
      rw [show φ_pre = kerZ_to_Is ≫ gen_s from h_func.symm]
      exact imageSubobject_comp_le _ _
    -- φ_pre factors through F_s = imageSubobject(gen_s)
    have h_fac_Fs : (imageSubobject gen_s).Factors φ_pre := by
      have : φ_pre = (kerZ_to_Is ≫ factorThruImageSubobject gen_s) ≫
          (imageSubobject gen_s).arrow := by
        rw [Category.assoc, imageSubobject_arrow_comp]
        exact h_func.symm
      rw [this]
      exact Subobject.factors_comp_arrow _
    let φ_to_Fs := Subobject.factorThru (imageSubobject gen_s) φ_pre h_fac_Fs
    have h_φ_to_Fs : φ_to_Fs ≫ (imageSubobject gen_s).arrow = φ_pre :=
      Subobject.factorThru_arrow _ _ h_fac_Fs
    -- Compose with cokernel projection to get kerZ → RHS
    -- RHS = cokernel(ofLE F_{s+1} F_s _)
    -- We need the cokernel.π for the RHS
    -- But first, F_s and F_{s+1} are from homologyFiltration, not our local gen_s/gen_s1.
    -- They should be definitionally equal (or propositionally equal)
    -- to imageSubobject gen_s / gen_s1.
    -- Let's show they match.
    -- ======================================
    -- CONSTRUCTION OF THE CONVERGENCE ISOMORPHISM
    -- E_∞ = Z_⊤/B_⊤ ≅ gr^s H_k = F_s H_k / F_{s+1} H_k
    --
    -- Forward: E_∞ → gr^s H_k via φ_to_Fs
    -- Inverse: gr^s H_k → E_∞ via kerZ.arrow ≫ πV
    -- ======================================
    -- Step 1: Forward map on Z_⊤
    -- We build fwd_Z : Z_⊤.underlying → gr^s H_k (the RHS)
    -- by descending φ_to_Fs ≫ cokernel.π through the epi
    -- factorThruImageSubobject(kerZ.arrow ≫ πV) : kerZ → Z_⊤
    -- The RHS cokernel projection
    let πRHS := cokernel.π (Subobject.ofLE
      (FC.homologySSFiltration.F (s + 1) k)
      (FC.homologySSFiltration.F s k)
      (FC.homologySSFiltration.mono s k))
    -- The composed map kerZ → gr^s H_k
    let fwd_kerZ := φ_to_Fs ≫ πRHS
    -- The epi from kerZ to Z_⊤
    let e_Z := factorThruImageSubobject (kerZ.arrow ≫ πV)
    -- Descent condition: kernel.ι(e_Z) ≫ fwd_kerZ = 0
    -- This says: if x ∈ kerZ with kerZ.arrow(x) ∈ F^{s+1}, then φ_to_Fs(x) ∈ F_{s+1} H_k
    have h_desc_fwd : kernel.ι e_Z ≫ fwd_kerZ = 0 := by
      -- kernel.ι e_Z ≫ (kerZ.arrow ≫ πV) = 0 (kernel condition + image factorization)
      have h_ker_πV : kernel.ι e_Z ≫ kerZ.arrow ≫ πV = 0 := by
        have h0 : kernel.ι e_Z ≫ e_Z = 0 := kernel.condition e_Z
        have h1 : factorThruImageSubobject (kerZ.arrow ≫ πV) ≫
            (imageSubobject (kerZ.arrow ≫ πV)).arrow =
            kerZ.arrow ≫ πV := by simp [imageSubobject_arrow_comp]
        calc kernel.ι e_Z ≫ kerZ.arrow ≫ πV
            = kernel.ι e_Z ≫ (e_Z ≫
                (imageSubobject (kerZ.arrow ≫ πV)).arrow) := by rw [h1]
          _ = (kernel.ι e_Z ≫ e_Z) ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow :=
                (Category.assoc _ _ _).symm
          _ = 0 ≫ _ := by rw [h0]
          _ = 0 := zero_comp
      -- Lift through ι_fil
      have h_ker_πV' : (kernel.ι e_Z ≫ kerZ.arrow) ≫ cokernel.π ι_fil = 0 := by
        rw [Category.assoc]; exact h_ker_πV
      set lift_s1 := Abelian.monoLift ι_fil (kernel.ι e_Z ≫ kerZ.arrow) h_ker_πV'
      have h_lift_s1 : lift_s1 ≫ ι_fil = kernel.ι e_Z ≫ kerZ.arrow :=
        Abelian.monoLift_comp _ _ _
      -- kernel.ι e_Z ≫ φ_to_X2 factors through I_{s+1} = ker(S.g) ∩ fil(s+1, k+1-1)
      set I_s1 := kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1)
      have h_zero_s1 : I_s1.arrow ≫ S.g = 0 := by
        rw [show I_s1.arrow = Subobject.ofLE I_s1 (kernelSubobject S.g)
            inf_le_left ≫ (kernelSubobject S.g).arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc, kernelSubobject_arrow_comp, comp_zero]
      set gen_s1 := S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ
      -- Key factorization: kernel.ι e_Z ≫ φ_to_X2 lies in I_{s+1}
      -- φ_to_X2 = kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg
      -- kernel.ι e_Z ≫ kerZ.arrow = lift_s1 ≫ ι_fil (h_lift_s1)
      -- So kernel.ι e_Z ≫ φ_to_X2 = lift_s1 ≫ ι_fil ≫ (fil s k).arrow ≫ eqToHom
      --   = lift_s1 ≫ (fil(s+1,k)).arrow ≫ eqToHom
      --   = (lift_s1 ≫ eqToHom_sub) ≫ (fil(s+1,k+1-1)).arrow
      -- which factors through fil(s+1,k+1-1).
      -- Also kernel.ι e_Z ≫ φ_to_X2 ≫ S.g = 0 (from h_lift).
      -- So it's in ker(S.g) ∩ fil(s+1,k+1-1) = I_{s+1}.
      -- Then kernel.ι e_Z ≫ φ_pre = α ≫ gen_s1 (liftCycles functoriality)
      -- = (α ≫ fTI gen_s1) ≫ (F_{s+1}).arrow
      -- And kernel.ι e_Z ≫ φ_to_Fs ≫ (F_s).arrow = kernel.ι e_Z ≫ φ_pre
      -- So kernel.ι e_Z ≫ φ_to_Fs = (α ≫ fTI gen_s1) ≫ ofLE(F_{s+1}, F_s) (mono cancel)
      -- Step B: factor kernel.ι e_Z ≫ φ_to_X2 through I_{s+1}
      have h_ι_arrow : ι_fil ≫ (FC.fil s k).arrow = (FC.fil (s + 1) k).arrow :=
        Subobject.ofLE_arrow (FC.fil_anti s k)
      have h_transport_s1 : (FC.fil (s + 1) k).arrow ≫ eqToHom e_deg =
          eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
            (show k = k + 1 - 1 by omega)) ≫
          (FC.fil (s + 1) (k + 1 - 1)).arrow := by
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil (s + 1) a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j)) h) ≫
            (FC.fil (s + 1) b).arrow := by
          intro a b h; subst h; simp
        exact this k (k + 1 - 1) (by omega)
      have h_ker_lift_sg : (kernel.ι e_Z ≫ φ_to_X2) ≫ S.g = 0 := by
        rw [Category.assoc]; exact (h_lift ▸ comp_zero)
      have h_ker_in_fil_s1 :
          (FC.fil (s + 1) (k + 1 - 1)).Factors (kernel.ι e_Z ≫ φ_to_X2) := by
        have h_eq : kernel.ι e_Z ≫ φ_to_X2 =
            (lift_s1 ≫ eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
              (show k = k + 1 - 1 by omega))) ≫
            (FC.fil (s + 1) (k + 1 - 1)).arrow := by
          change kernel.ι e_Z ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) = _
          rw [show kernel.ι e_Z ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
              (kernel.ι e_Z ≫ kerZ.arrow) ≫ ((FC.fil s k).arrow ≫ eqToHom e_deg) by
            simp only [Category.assoc]]
          rw [h_lift_s1.symm]
          rw [show (lift_s1 ≫ ι_fil) ≫ ((FC.fil s k).arrow ≫ eqToHom e_deg) =
              lift_s1 ≫ (ι_fil ≫ (FC.fil s k).arrow) ≫ eqToHom e_deg by
            simp only [Category.assoc]]
          rw [h_ι_arrow, h_transport_s1]
          simp only [Category.assoc]
        rw [h_eq]; exact Subobject.factors_comp_arrow _
      have h_fac_I_s1 : I_s1.Factors (kernel.ι e_Z ≫ φ_to_X2) := by
        rw [show I_s1 = kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1) from rfl,
            Subobject.inf_factors]
        exact ⟨kernelSubobject_factors S.g _ h_ker_lift_sg, h_ker_in_fil_s1⟩
      let ker_to_I_s1 := Subobject.factorThru I_s1 (kernel.ι e_Z ≫ φ_to_X2) h_fac_I_s1
      have h_ker_to_I_s1 : ker_to_I_s1 ≫ I_s1.arrow = kernel.ι e_Z ≫ φ_to_X2 :=
        Subobject.factorThru_arrow _ _ _
      -- Step C: liftCycles functoriality
      have h_func_s1 : ker_to_I_s1 ≫ gen_s1 = kernel.ι e_Z ≫ φ_pre := by
        change ker_to_I_s1 ≫ (S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ) =
          kernel.ι e_Z ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ)
        rw [← Category.assoc, ← Category.assoc]; congr 1
        apply (cancel_mono S.iCycles).mp
        rw [Category.assoc, S.liftCycles_i, Category.assoc, S.liftCycles_i, h_ker_to_I_s1]
      -- Step D: factor through ofLE(F_{s+1}, F_s)
      have h_Fs1_le_Fs : FC.homologySSFiltration.F (s + 1) k ≤
          FC.homologySSFiltration.F s k :=
        FC.homologySSFiltration.mono s k
      have h_ofLE_arrow : Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
          (FC.homologySSFiltration.F s k) h_Fs1_le_Fs ≫
          (FC.homologySSFiltration.F s k).arrow =
          (FC.homologySSFiltration.F (s + 1) k).arrow :=
        Subobject.ofLE_arrow h_Fs1_le_Fs
      have h_factor_ofLE : kernel.ι e_Z ≫ φ_to_Fs =
          (ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
          Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
            (FC.homologySSFiltration.F s k) h_Fs1_le_Fs := by
        apply (cancel_mono (imageSubobject gen_s).arrow).mp
        rw [Category.assoc, h_φ_to_Fs]
        -- LHS: kernel.ι e_Z ≫ φ_pre
        -- RHS: ((ker_to_I_s1 ≫ fTI gen_s1) ≫ ofLE) ≫ (imageSubobject gen_s).arrow
        -- Rewrite RHS to ker_to_I_s1 ≫ gen_s1 = kernel.ι e_Z ≫ φ_pre
        have h_rhs : ((ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
            Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
              (FC.homologySSFiltration.F s k) h_Fs1_le_Fs) ≫
            (imageSubobject gen_s).arrow =
            ker_to_I_s1 ≫ gen_s1 := by
          -- (imageSubobject gen_s).arrow = (FC.homologySSFiltration.F s k).arrow definitionally
          change ((ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
            Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
              (FC.homologySSFiltration.F s k) h_Fs1_le_Fs) ≫
            (FC.homologySSFiltration.F s k).arrow = ker_to_I_s1 ≫ gen_s1
          simp only [Category.assoc]
          rw [h_ofLE_arrow]
          -- Now: ker_to_I_s1 ≫ fTI gen_s1 ≫ (imageSubobject gen_s1).arrow
          -- = ker_to_I_s1 ≫ gen_s1
          -- (FC.homologySSFiltration.F (s+1) k).arrow = (imageSubobject gen_s1).arrow definitionally
          change ker_to_I_s1 ≫ factorThruImageSubobject gen_s1 ≫
            (imageSubobject gen_s1).arrow = ker_to_I_s1 ≫ gen_s1
          rw [imageSubobject_arrow_comp]
        rw [h_rhs]
        exact h_func_s1.symm
      -- Step E: compose with πRHS = cokernel.π → 0
      change kernel.ι e_Z ≫ (φ_to_Fs ≫ πRHS) = 0
      rw [← Category.assoc, h_factor_ofLE, Category.assoc, Category.assoc]
      rw [show Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
            (FC.homologySSFiltration.F s k) h_Fs1_le_Fs ≫ πRHS = 0
        from cokernel.condition _]
      rw [comp_zero, comp_zero]
    -- Descended map on Z_⊤
    let fwd_Z := Abelian.epiDesc e_Z fwd_kerZ h_desc_fwd
    -- Property: e_Z ≫ fwd_Z = fwd_kerZ
    have h_fwd_Z : e_Z ≫ fwd_Z = fwd_kerZ := Abelian.comp_epiDesc _ _ _
    -- Step 2: Show fwd_Z kills B_⊤
    -- Need: ofLE(B_⊤, Z_⊤, _) ≫ fwd_Z = 0
    have h_fwd_kills_B : Subobject.ofLE
        ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
        ((FC.toSSData bnd s k).B_le_Z ⊤) ≫ fwd_Z = 0 := by
      -- === Proof that fwd_Z kills B_⊤ ===
      -- Local boundary notation
      let imgD := imageSubobject (FC.dToK k)
      let I_B := imgD ⊓ FC.fil s k
      let oI := Subobject.ofLE I_B (FC.fil s k) inf_le_right
      -- oI ≫ f_Z = 0 (boundary elements are cycles)
      have h_oI_zero : oI ≫ f_Z = 0 := by
        change Subobject.ofLE I_B (FC.fil s k) inf_le_right ≫
          (FC.fil s k).arrow ≫ FC.d k = 0
        rw [← Category.assoc, Subobject.ofLE_arrow]
        rw [show I_B.arrow =
            Subobject.ofLE I_B imgD inf_le_left ≫ imgD.arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, comp_zero]
      -- Factor oI through kerZ
      let oI_lift := factorThruKernelSubobject f_Z oI h_oI_zero
      have h_oI_lift : oI_lift ≫ kerZ.arrow = oI :=
        factorThruKernelSubobject_comp_arrow f_Z oI h_oI_zero
      -- Step A: factorThruImageSubobject(oI ≫ πV) ≫ ofLE(B,Z) = oI_lift ≫ e_Z
      have h_fti_ofLE : factorThruImageSubobject (oI ≫ πV) ≫
          Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
          ((FC.toSSData bnd s k).B_le_Z ⊤) = oI_lift ≫ e_Z := by
        apply (cancel_mono ((FC.toSSData bnd s k).Z ⊤).arrow).mp
        rw [Category.assoc, Subobject.ofLE_arrow]
        change factorThruImageSubobject (oI ≫ πV) ≫
          ((FC.toSSData bnd s k).B ⊤).arrow = (oI_lift ≫ e_Z) ≫ _
        rw [show ((FC.toSSData bnd s k).B ⊤).arrow =
            (imageSubobject (oI ≫ πV)).arrow from rfl]
        rw [imageSubobject_arrow_comp]
        rw [Category.assoc]
        rw [show e_Z ≫ ((FC.toSSData bnd s k).Z ⊤).arrow =
          kerZ.arrow ≫ πV from imageSubobject_arrow_comp (kerZ.arrow ≫ πV)]
        rw [← Category.assoc, h_oI_lift]
      -- Step B: Cancel epi
      rw [← cancel_epi (factorThruImageSubobject (oI ≫ πV))]
      rw [comp_zero, ← Category.assoc, h_fti_ofLE]
      -- Goal: (oI_lift ≫ e_Z) ≫ fwd_Z = 0
      rw [Category.assoc, h_fwd_Z]
      -- Goal: oI_lift ≫ fwd_kerZ = 0
      change oI_lift ≫ (φ_to_Fs ≫ πRHS) = 0
      rw [← Category.assoc]
      -- Step C: Show oI_lift ≫ φ_to_Fs = 0
      suffices h_oI_φ_to_Fs : oI_lift ≫ φ_to_Fs = 0 by
        rw [h_oI_φ_to_Fs, zero_comp]
      apply (cancel_mono (imageSubobject gen_s).arrow).mp
      rw [Category.assoc, h_φ_to_Fs, zero_comp]
      -- Goal: oI_lift ≫ φ_pre = 0
      change oI_lift ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ) = 0
      rw [← Category.assoc]
      -- Step D: oI_lift ≫ φ_to_X2 = I_B.arrow ≫ eqToHom e_deg
      have h_comp_φ : oI_lift ≫ φ_to_X2 = I_B.arrow ≫ eqToHom e_deg := by
        change oI_lift ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
          I_B.arrow ≫ eqToHom e_deg
        rw [← Category.assoc, ← Category.assoc,
          show oI_lift ≫ kerZ.arrow = oI from h_oI_lift,
          show oI ≫ (FC.fil s k).arrow = I_B.arrow
            from Subobject.ofLE_arrow inf_le_right]
      -- Step E: I_B.arrow ≫ eqToHom = ofLE(I_B, imgD, _) ≫ imgD.arrow ≫ eqToHom
      have h_IB_factor : I_B.arrow ≫ eqToHom e_deg =
          Subobject.ofLE I_B imgD inf_le_left ≫ (imgD.arrow ≫ eqToHom e_deg) := by
        rw [← Category.assoc, Subobject.ofLE_arrow]
      -- Step F: imgD.arrow ≫ eqToHom ≫ S.g = 0
      have h_imgD_sg : (imgD.arrow ≫ eqToHom e_deg) ≫ S.g = 0 := by
        rw [Category.assoc]
        have h_eqToHom_sg : eqToHom e_deg ≫ S.g =
            FC.d k ≫ eqToHom (congr_arg FC.A (show k - 1 = (k + 1 - 1) - 1 by omega)) := by
          suffices h : ∀ (n : ℤ) (hn : n = k),
              eqToHom (show FC.A k = FC.A n from congr_arg FC.A hn.symm) ≫ FC.d n =
              FC.d k ≫ eqToHom (show FC.A (k - 1) = FC.A (n - 1) from
                congr_arg FC.A (show k - 1 = n - 1 by omega)) by
            convert h (k + 1 - 1) (by omega) using 1
          intro n hn; subst hn; simp [eqToHom_refl, Category.id_comp, Category.comp_id]
        rw [h_eqToHom_sg, ← Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, zero_comp]
      -- Step G: S.liftCycles(imgD.arrow ≫ eqToHom) ≫ S.homologyπ = 0
      have h_imgD_homologyπ :
          S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg ≫ S.homologyπ = 0 := by
        rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
        rw [comp_zero, ← Category.assoc]
        have h_fti_lc : factorThruImageSubobject (FC.dToK k) ≫
            S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg = S.toCycles := by
          apply (cancel_mono S.iCycles).mp
          rw [Category.assoc, S.liftCycles_i, S.toCycles_i]
          rw [← Category.assoc, imageSubobject_arrow_comp]
          change FC.dToK k ≫ eqToHom e_deg = S.f
          change FC.complex.d (k + 1) k ≫ eqToHom e_deg =
            FC.complex.d (k + 1) (k + 1 - 1)
          exact FC.complex_d_comp_eqToHom (k + 1)
            (show k = k + 1 - 1 by omega)
        rw [h_fti_lc, S.toCycles_comp_homologyπ]
      -- Step H: liftCycles functoriality chain
      have h_comp_sg : (oI_lift ≫ φ_to_X2) ≫ S.g = 0 := by
        rw [Category.assoc]; exact h_lift ▸ comp_zero
      have h_IB_sg : (I_B.arrow ≫ eqToHom e_deg) ≫ S.g = 0 := by
        rw [h_comp_φ.symm]; exact h_comp_sg
      have h_lc_func : oI_lift ≫ S.liftCycles φ_to_X2 h_lift =
          S.liftCycles (oI_lift ≫ φ_to_X2) h_comp_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [Category.assoc, S.liftCycles_i, S.liftCycles_i]
      rw [h_lc_func]
      have h_lc_eq : S.liftCycles (oI_lift ≫ φ_to_X2) h_comp_sg =
          S.liftCycles (I_B.arrow ≫ eqToHom e_deg) h_IB_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, S.liftCycles_i, h_comp_φ]
      rw [h_lc_eq]
      have h_lc_factor : S.liftCycles (I_B.arrow ≫ eqToHom e_deg) h_IB_sg =
          Subobject.ofLE I_B imgD inf_le_left ≫
          S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, Category.assoc, S.liftCycles_i, h_IB_factor]
      rw [h_lc_factor, Category.assoc, h_imgD_homologyπ, comp_zero]
    -- Step 3: Forward map E_∞ → gr^s H_k
    let fwd := cokernel.desc _ fwd_Z h_fwd_kills_B
    -- Step 4: Inverse map on F_s H_k
    -- We build inv_Fs : F_s.underlying → E_∞ (the LHS)
    -- by descending through the epi factorThruImageSubobject(gen_s) : I_s → F_s
    -- The LHS cokernel projection
    let πLHS := cokernel.π (Subobject.ofLE
      ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
      ((FC.toSSData bnd s k).B_le_Z ⊤))
    -- The epi from I_s to F_s H_k
    let e_Fs := factorThruImageSubobject gen_s
    -- The composed map I_s → E_∞
    -- We need: I_s → kerZ → Z_⊤ → E_∞
    -- The map I_s → Z_⊤ is: kerZ_to_Is ≫ e_Z
    -- (but kerZ_to_Is : kerZ → I_s, wrong direction!)
    -- Instead: we need the map I_s → kerZ, which requires eqToHom transport.
    -- Use: e_Z ≫ πLHS composed with the factorization through kerZ_to_Is
    -- Alternative: compose directly. We know kerZ_to_Is ≫ gen_s = φ_pre = h_func
    -- So kerZ_to_Is ≫ e_Fs ≫ ... But this still goes kerZ → I_s → F_s, not I_s → kerZ.
    -- The right approach: the map I_s → E_∞ goes through the arrow:
    -- I_s.arrow : I_s.underlying → A(k+1-1)
    -- Transport to A(k) via eqToHom⁻¹ to get an element in (fil s k) ∩ ker(d k)
    -- Then project to V and down to E_∞.
    -- This is complex, so we abstract it.
    -- Map: I_s → Z_⊤ using the factorization I_s → kerZ → Z_⊤
    -- For I_s → kerZ: since I_s is a subobject of A(k+1-1) in ker(S.g) ∩ fil s (k+1-1),
    -- and kerZ is a subobject of (fil s k).underlying in ker(d k),
    -- we need to transport and factor.
    -- For now, construct the inverse using the abstract approach:
    -- inv_Is : I_s → E_∞ will be defined, then descended through e_Fs.
    -- The map I_s → kerZ.underlying
    -- I_s.arrow = (ofLE I_s (ker S.g) inf_le_left ≫ (ker S.g).arrow) needs to go to kerZ
    -- via eqToHom transport. Factor through (fil s k).
    -- Since φ_to_X2 = kerZ.arrow ≫ (fil s k).arrow ≫ eqToHom e_deg
    -- and I_s.arrow has I_s ≤ fil s (k+1-1),
    -- the key is that kerZ_to_Is ≫ I_s.arrow = φ_to_X2
    -- = kerZ.arrow ≫ (fil s k).arrow ≫ eqToHom e_deg
    -- The inverse map I_s.underlying → E_∞:
    -- Use kerZ_to_Is in the reverse: we cannot directly invert it.
    -- Instead, build a different composition.
    -- Alternative cleaner approach: since kerZ_to_Is ≫ gen_s = φ_pre (h_func),
    -- we have kerZ_to_Is ≫ e_Fs = kerZ_to_Is ≫ factorThruImageSubobject gen_s
    -- And e_Z = factorThruImageSubobject (kerZ.arrow ≫ πV)
    -- Both are related via the commutative square.
    -- Let's build the inverse differently:
    -- inv_Is : I_s.underlying → E_∞ is defined below
    -- and then descended through the epi e_Fs.
    -- The inverse I_s → E_∞ goes through:
    -- I_s →[ofLE I_s (fil s (k+1-1)) inf_le_right] (fil s (k+1-1)).underlying
    -- →[eqToHom⁻¹] (fil s k).underlying →[needs: in ker(d k)] kerZ.underlying
    -- →[kerZ.arrow] (fil s k).underlying →[πV] V →[into Z_⊤]
    -- But this is circular (we go to fil s k then back).
    -- Actually simpler: define inv_Is using factorThruKernelSubobject:
    -- From I_s we get an element of A(k+1-1) that's in ker(S.g) ∩ fil s (k+1-1).
    -- This element is in ker(S.g) means S.g(x) = 0, i.e., d(k+1-1)(x) = 0.
    -- Transport: eqToHom(e_deg)⁻¹(x) ∈ A(k), and d(k)(eqToHom⁻¹(x)) = 0 (up to transport).
    -- Also eqToHom⁻¹(x) ∈ fil s k. So eqToHom⁻¹ factors through (fil s k).arrow.
    -- The factored element y satisfies (fil s k).arrow(y) ≫ d k = 0, so y ∈ kerZ.
    -- Let's define the transport map:
    let e_deg_inv : FC.A (k + 1 - 1) = FC.A k :=
      congr_arg FC.A (show k + 1 - 1 = k by omega)
    -- I_s.arrow ≫ eqToHom(e_deg_inv) : I_s.underlying → A(k)
    -- This factors through (fil s k).arrow because
    -- I_s ≤ fil s (k+1-1) and eqToHom transports fil.
    -- Then it's in ker(d k) because I_s ≤ ker(S.g) and S.g ≈ d(k+1-1) which transports to d(k).
    -- Construct map I_s → (fil s k).underlying
    have h_Is_to_fil : (FC.fil s k).Factors (I_s.arrow ≫ eqToHom e_deg_inv) := by
      -- I_s ≤ fil s (k+1-1), and eqToHom transports fil s (k+1-1) to fil s k
      have h_le : I_s ≤ FC.fil s (k + 1 - 1) := inf_le_right
      have h_arrow : I_s.arrow = Subobject.ofLE I_s (FC.fil s (k + 1 - 1)) h_le ≫
          (FC.fil s (k + 1 - 1)).arrow := (Subobject.ofLE_arrow h_le).symm
      rw [h_arrow, Category.assoc]
      -- Now need: (fil s (k+1-1)).arrow ≫ eqToHom e_deg_inv = eqToHom(...) ≫ (fil s k).arrow
      have h_transport2 : (FC.fil s (k + 1 - 1)).arrow ≫ eqToHom e_deg_inv =
          eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j))
            (show k + 1 - 1 = k by omega)) ≫ (FC.fil s k).arrow := by
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil s a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j)) h) ≫
            (FC.fil s b).arrow := by
          intro a b h; subst h; simp
        exact this (k + 1 - 1) k (by omega)
      rw [h_transport2, ← Category.assoc]
      exact Subobject.factors_comp_arrow _
    let Is_to_fil := Subobject.factorThru (FC.fil s k) (I_s.arrow ≫ eqToHom e_deg_inv) h_Is_to_fil
    have h_Is_to_fil_eq : Is_to_fil ≫ (FC.fil s k).arrow = I_s.arrow ≫ eqToHom e_deg_inv :=
      Subobject.factorThru_arrow _ _ _
    -- Show Is_to_fil ∈ ker(f_Z)
    have h_Is_in_kerZ : Is_to_fil ≫ f_Z = 0 := by
      change Is_to_fil ≫ ((FC.fil s k).arrow ≫ FC.d k) = 0
      rw [← Category.assoc,
        show (Is_to_fil ≫ (FC.fil s k).arrow) =
          I_s.arrow ≫ eqToHom e_deg_inv
        from h_Is_to_fil_eq, Category.assoc]
      -- Need: eqToHom e_deg_inv ≫ d k = S.g ≫ eqToHom(...)
      -- Since S.g = d(k+1-1) and e_deg_inv : A(k+1-1) = A(k),
      -- eqToHom(e_deg_inv) ≫ d k = d(k+1-1) ≫ eqToHom(...) (up to degree transport)
      -- But actually: S.g = d(k+1-1) with source A(k+1-1) and target A((k+1-1)-1).
      -- d k has source A(k) and target A(k-1).
      -- eqToHom e_deg_inv : A(k+1-1) ⟶ A(k). So eqToHom ≫ d k : A(k+1-1) → A(k-1).
      -- S.g = d(k+1-1) : A(k+1-1) → A((k+1-1)-1) = A(k-1-1+1) ... this needs care.
      -- Actually S = ShortComplex.mk (d(k+1)) (d(k+1-1)) _, so S.g = d(k+1-1).
      -- S.g : S.X₂ → S.X₃ where S.X₂ = A(k+1-1), S.X₃ = A((k+1-1)-1).
      -- Now d k : A(k) → A(k-1) and (k+1-1)-1 = k-1, so S.X₃ = A(k-1).
      -- eqToHom(e_deg_inv) : A(k+1-1) → A(k). So eqToHom ≫ d k : A(k+1-1) → A(k-1).
      -- S.g = d(k+1-1) : A(k+1-1) → A((k+1-1)-1). Now (k+1-1)-1 = k-1 (by omega).
      -- So eqToHom ≫ d k and S.g both go A(k+1-1) → A(k-1) (up to eqToHom on target).
      -- More precisely: eqToHom(e_deg_inv) ≫ d k = S.g ≫ eqToHom(A((k+1-1)-1) = A(k-1)).
      -- So I_s.arrow ≫ eqToHom ≫ d k
      -- = I_s.arrow ≫ S.g ≫ eqToHom = 0 (since I_s ≤ ker S.g).
      have h_transport_d : eqToHom e_deg_inv ≫ FC.d k =
          S.g ≫ eqToHom (congr_arg FC.A (show (k + 1 - 1) - 1 = k - 1 by omega)) := by
        simp [S]
      rw [h_transport_d, ← Category.assoc]
      -- I_s.arrow ≫ S.g = 0 (since I_s ≤ ker S.g)
      have h_Is_ker : I_s.arrow ≫ S.g = 0 := h_zero_s
      rw [h_Is_ker, zero_comp]
    -- Factor Is_to_fil through kerZ
    let Is_to_kerZ := factorThruKernelSubobject f_Z Is_to_fil h_Is_in_kerZ
    -- Property: Is_to_kerZ ≫ kerZ.arrow = Is_to_fil
    have h_Is_to_kerZ : Is_to_kerZ ≫ kerZ.arrow = Is_to_fil :=
      factorThruKernelSubobject_comp_arrow _ _ _
    -- The composed map I_s → E_∞
    let inv_Is := Is_to_kerZ ≫ e_Z ≫ πLHS
    -- Descent condition for the inverse: kernel.ι(e_Fs) ≫ inv_Is = 0
    have h_desc_inv : kernel.ι e_Fs ≫ inv_Is = 0 := by
      -- ═══ Step 1: kernel.ι e_Fs ≫ gen_s = 0 ═══
      have h_ker_gen : kernel.ι e_Fs ≫ gen_s = 0 := by
        -- gen_s = e_Fs ≫ (imageSubobject gen_s).arrow, and kernel.ι e_Fs ≫ e_Fs = 0
        have h_assoc : kernel.ι e_Fs ≫ e_Fs ≫ (imageSubobject gen_s).arrow = 0 := by
          rw [kernel.condition_assoc, zero_comp]
        rwa [imageSubobject_arrow_comp] at h_assoc
      have h_lc_π : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫ S.homologyπ = 0 := by
        rw [Category.assoc]; exact h_ker_gen
      -- Step 2: kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom
      -- ≫ cokernel.π(dToK k) = 0
      have h_Sf_dToK : S.f ≫ eqToHom e_deg_inv = FC.dToK k := by
        change FC.complex.d (k + 1) (k + 1 - 1) ≫ eqToHom e_deg_inv =
          FC.complex.d (k + 1) k
        exact FC.complex_d_comp_eqToHom (k + 1)
          (show k + 1 - 1 = k by omega)
      have h_comp_cok_dToK : (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) ≫
          cokernel.π (FC.dToK k) = 0 := by
        -- Transfer h_lc_π to cokernel.π(S.toCycles)
        have h_φ_lHπ : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫
            S.leftHomologyπ = 0 := by
          have hπ_eq : S.homologyπ = S.leftHomologyπ ≫ S.leftHomologyIso.hom := by
            rw [← Category.comp_id S.homologyπ,
                ← Iso.inv_hom_id S.leftHomologyIso, ← Category.assoc,
                S.homologyπ_comp_leftHomologyIso_inv]
          rw [← cancel_mono S.leftHomologyIso.hom, Category.assoc, zero_comp, ← hπ_eq]
          exact h_lc_π
        have h_φ_cok_tC : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫
            cokernel.π S.toCycles = 0 := by
          let σ := IsColimit.coconePointUniqueUpToIso S.leftHomologyIsCokernel
              (cokernelIsCokernel S.toCycles)
          have : S.leftHomologyπ ≫ σ.hom = cokernel.π S.toCycles :=
            IsColimit.comp_coconePointUniqueUpToIso_hom S.leftHomologyIsCokernel
              (cokernelIsCokernel S.toCycles) WalkingParallelPair.one
          rw [← this, ← Category.assoc, h_φ_lHπ, zero_comp]
        -- Factor through kernel(cokernel.π S.toCycles) = Abelian.image(S.toCycles)
        let κ := kernel.lift (cokernel.π S.toCycles)
            (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) h_φ_cok_tC
        have hκ : κ ≫ kernel.ι (cokernel.π S.toCycles) =
            kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s := kernel.lift_ι _ _ _
        -- kernel.ι e_Fs ≫ I_s.arrow = κ ≫ kernel.ι(cokernel.π S.toCycles) ≫ S.iCycles
        have hκ_arrow : κ ≫ (kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles) =
            kernel.ι e_Fs ≫ I_s.arrow := by
          rw [← Category.assoc, hκ, Category.assoc, S.liftCycles_i]
        -- Abelian.factorThruImage ≫ kernel.ι(cokernel.π S.toCycles) = S.toCycles
        have h_img_fac : Abelian.factorThruImage S.toCycles ≫
            kernel.ι (cokernel.π S.toCycles) = S.toCycles := Abelian.image.fac S.toCycles
        -- kernel.ι(cokernel.π S.toCycles) ≫ S.iCycles ≫ eqToHom ≫ cokernel.π(dToK k) = 0
        have h_mid_zero : kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles ≫
            eqToHom e_deg_inv ≫ cokernel.π (FC.dToK k) = 0 := by
          rw [← cancel_epi (Abelian.factorThruImage S.toCycles), comp_zero]
          simp only [← Category.assoc]
          rw [h_img_fac, S.toCycles_i, h_Sf_dToK, cokernel.condition]
        -- Conclude
        -- Goal: (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv)
        -- ≫ cokernel.π (FC.dToK k) = 0
        -- Rewrite kernel.ι e_Fs ≫ I_s.arrow using hκ_arrow (left-associated)
        have h_sub : kernel.ι e_Fs ≫ I_s.arrow =
            κ ≫ (kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles) := hκ_arrow.symm
        -- Left-associate everything so kernel.ι e_Fs ≫ I_s.arrow is a subterm
        simp only [← Category.assoc] at h_sub ⊢
        rw [h_sub]
        simp only [Category.assoc]
        rw [h_mid_zero, comp_zero]
      -- ═══ Step 3: Factor through imageSubobject(dToK k) ═══
      -- In abelian categories, imageSubobject f = kernelSubobject(cokernel.π f)
      -- So factoring through imageSubobject reduces to: comp with cokernel.π = 0
      have h_imgD_eq_kerCok : imageSubobject (FC.dToK k) =
          kernelSubobject (cokernel.π (FC.dToK k)) := by
        have hex := ShortComplex.exact_cokernel (FC.dToK k)
        rwa [ShortComplex.exact_iff_image_eq_kernel] at hex
      have h_in_imgD : (imageSubobject (FC.dToK k)).Factors
          (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [h_imgD_eq_kerCok, kernelSubobject_factors_iff]
        exact h_comp_cok_dToK
      -- ═══ Step 4: Also in fil s k (trivial) ═══
      have h_in_fil : (FC.fil s k).Factors
          (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [show kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv =
          (kernel.ι e_Fs ≫ Is_to_fil) ≫ (FC.fil s k).arrow from by
          rw [Category.assoc, h_Is_to_fil_eq]]
        exact Subobject.factors_comp_arrow _
      -- ═══ Step 5: Factor through I_B = imgD ⊓ fil s k ═══
      let imgD := imageSubobject (FC.dToK k)
      let I_B := imgD ⊓ FC.fil s k
      have h_in_IB : I_B.Factors (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [show I_B = imgD ⊓ FC.fil s k from rfl, Subobject.inf_factors]
        exact ⟨h_in_imgD, h_in_fil⟩
      let ker_to_IB := I_B.factorThru (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) h_in_IB
      have h_ker_to_IB : ker_to_IB ≫ I_B.arrow =
          kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv :=
        Subobject.factorThru_arrow _ _ _
      -- ═══ Step 6: Local oI and oI_lift ═══
      let oI := Subobject.ofLE I_B (FC.fil s k) inf_le_right
      have h_oI_zero : oI ≫ f_Z = 0 := by
        change Subobject.ofLE I_B (FC.fil s k) inf_le_right ≫
          (FC.fil s k).arrow ≫ FC.d k = 0
        rw [← Category.assoc, Subobject.ofLE_arrow]
        rw [show I_B.arrow = Subobject.ofLE I_B imgD inf_le_left ≫ imgD.arrow
          from (Subobject.ofLE_arrow inf_le_left).symm, Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, comp_zero]
      let oI_lift := factorThruKernelSubobject f_Z oI h_oI_zero
      have h_oI_lift : oI_lift ≫ kerZ.arrow = oI :=
        factorThruKernelSubobject_comp_arrow f_Z oI h_oI_zero
      -- ═══ Step 7: kernel.ι e_Fs ≫ Is_to_kerZ = ker_to_IB ≫ oI_lift ═══
      have h_factor_kerZ : kernel.ι e_Fs ≫ Is_to_kerZ = ker_to_IB ≫ oI_lift := by
        apply (cancel_mono kerZ.arrow).mp
        simp only [Category.assoc]
        rw [h_oI_lift, h_Is_to_kerZ]
        apply (cancel_mono (FC.fil s k).arrow).mp
        simp only [Category.assoc]
        rw [Subobject.ofLE_arrow, h_ker_to_IB, h_Is_to_fil_eq]
      -- ═══ Step 8: oI_lift ≫ e_Z ≫ πLHS = 0 ═══
      have h_fti_ofLE : factorThruImageSubobject (oI ≫ πV) ≫
          Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
          ((FC.toSSData bnd s k).B_le_Z ⊤) = oI_lift ≫ e_Z := by
        apply (cancel_mono ((FC.toSSData bnd s k).Z ⊤).arrow).mp
        rw [Category.assoc, Subobject.ofLE_arrow]
        change factorThruImageSubobject (oI ≫ πV) ≫
          ((FC.toSSData bnd s k).B ⊤).arrow = (oI_lift ≫ e_Z) ≫ _
        rw [show ((FC.toSSData bnd s k).B ⊤).arrow =
            (imageSubobject (oI ≫ πV)).arrow from rfl]
        rw [imageSubobject_arrow_comp, Category.assoc]
        rw [show e_Z ≫ ((FC.toSSData bnd s k).Z ⊤).arrow =
          kerZ.arrow ≫ πV from imageSubobject_arrow_comp (kerZ.arrow ≫ πV)]
        rw [← Category.assoc, h_oI_lift]
      have h_oI_kill : oI_lift ≫ e_Z ≫ πLHS = 0 := by
        rw [← Category.assoc, ← h_fti_ofLE, Category.assoc]
        rw [show Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
            ((FC.toSSData bnd s k).B_le_Z ⊤) ≫ πLHS = 0 from cokernel.condition _]
        rw [comp_zero]
      -- ═══ Step 9: Conclude ═══
      change kernel.ι e_Fs ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = 0
      rw [← Category.assoc, ← Category.assoc, h_factor_kerZ,
          Category.assoc, Category.assoc, h_oI_kill, comp_zero]
    -- Descended map on F_s H_k
    let inv_Fs := Abelian.epiDesc e_Fs inv_Is h_desc_inv
    have h_inv_Fs : e_Fs ≫ inv_Fs = inv_Is := Abelian.comp_epiDesc _ _ _
    -- Show inv_Fs kills F_{s+1} H_k
    have h_inv_kills_Fs1 : Subobject.ofLE
        (FC.homologySSFiltration.F (s + 1) k)
        (FC.homologySSFiltration.F s k)
        (FC.homologySSFiltration.mono s k) ≫ inv_Fs = 0 := by
      -- Setup: redefine I_s1, gen_s1 (these were local to h_desc_fwd's scope)
      set I_s1 := kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1)
      have h_zero_s1 : I_s1.arrow ≫ S.g = 0 := by
        rw [show I_s1.arrow = Subobject.ofLE I_s1 (kernelSubobject S.g)
            inf_le_left ≫ (kernelSubobject S.g).arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc, kernelSubobject_arrow_comp, comp_zero]
      set gen_s1 := S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ
      -- The inclusion I_s1 ≤ I_s
      have hle : I_s1 ≤ I_s := inf_le_inf_left _ (FC.fil_anti s (k + 1 - 1))
      -- Key factorization: gen_s1 = ofLE(I_s1, I_s) ≫ gen_s
      have hlift_s : S.liftCycles I_s1.arrow h_zero_s1 =
          Subobject.ofLE I_s1 I_s hle ≫ S.liftCycles I_s.arrow h_zero_s := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, Category.assoc, S.liftCycles_i]
        exact (Subobject.ofLE_arrow hle).symm
      have h_gen_factor : gen_s1 =
          Subobject.ofLE I_s1 I_s hle ≫ gen_s := by
        change S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ =
          Subobject.ofLE I_s1 I_s hle ≫ (S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ)
        rw [← Category.assoc, hlift_s]
      -- Step 1: reduce via zero_of_epi_comp with factorThruImageSubobject gen_s1
      apply zero_of_epi_comp (factorThruImageSubobject gen_s1)
      -- Goal: factorThruImageSubobject gen_s1 ≫ ofLE(F_{s+1}, F_s) ≫ inv_Fs = 0
      -- Step 2: relate fTI gen_s1 ≫ ofLE(F_{s+1}, F_s) to ofLE(I_s1, I_s) ≫ fTI gen_s
      have h_fTI_ofLE : factorThruImageSubobject gen_s1 ≫
          Subobject.ofLE (FC.homologySSFiltration.F (s + 1) k)
            (FC.homologySSFiltration.F s k) (FC.homologySSFiltration.mono s k) =
          Subobject.ofLE I_s1 I_s hle ≫ factorThruImageSubobject gen_s := by
        -- Both sides are morphisms I_s1.underlying → (F_s).underlying
        -- (F_s).arrow is mono, cancel it
        apply (cancel_mono (FC.homologySSFiltration.F s k).arrow).mp
        -- LHS: fTI gen_s1 ≫ ofLE(F_{s+1}, F_s) ≫ (F_s).arrow
        --     = fTI gen_s1 ≫ (F_{s+1}).arrow  (by ofLE_arrow)
        --     = gen_s1                          (by imageSubobject_arrow_comp)
        rw [Category.assoc, Subobject.ofLE_arrow (FC.homologySSFiltration.mono s k)]
        change factorThruImageSubobject gen_s1 ≫ (imageSubobject gen_s1).arrow =
          (Subobject.ofLE I_s1 I_s hle ≫ factorThruImageSubobject gen_s) ≫
            (imageSubobject gen_s).arrow
        rw [imageSubobject_arrow_comp, Category.assoc, imageSubobject_arrow_comp]
        exact h_gen_factor
      -- Step 3: substitute and rewrite
      -- Goal: fTI gen_s1 ≫ ofLE(F_{s+1}, F_s) ≫ inv_Fs = 0
      -- Reassociate to (fTI gen_s1 ≫ ofLE(F_{s+1}, F_s)) ≫ inv_Fs
      rw [← Category.assoc, h_fTI_ofLE, Category.assoc]
      -- Goal: ofLE(I_s1, I_s) ≫ (factorThruImageSubobject gen_s ≫ inv_Fs) = 0
      -- factorThruImageSubobject gen_s = e_Fs
      change Subobject.ofLE I_s1 I_s hle ≫ (e_Fs ≫ inv_Fs) = 0
      rw [h_inv_Fs]
      -- Goal: ofLE(I_s1, I_s) ≫ inv_Is = 0
      -- inv_Is = Is_to_kerZ ≫ e_Z ≫ πLHS
      change Subobject.ofLE I_s1 I_s hle ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = 0
      rw [← Category.assoc, ← Category.assoc]
      -- Suffices: (ofLE(I_s1, I_s) ≫ Is_to_kerZ) ≫ e_Z = 0
      suffices h_zero : (Subobject.ofLE I_s1 I_s hle ≫ Is_to_kerZ) ≫ e_Z = 0 by
        rw [h_zero, zero_comp]
      -- Cancel mono: (imageSubobject (kerZ.arrow ≫ πV)).arrow is mono
      apply (cancel_mono (imageSubobject (kerZ.arrow ≫ πV)).arrow).mp
      rw [Category.assoc, imageSubobject_arrow_comp, zero_comp]
      -- Goal: (ofLE(I_s1, I_s) ≫ Is_to_kerZ) ≫ kerZ.arrow ≫ πV = 0
      -- Reassociate: ((ofLE ≫ Is_to_kerZ) ≫ kerZ.arrow) ≫ πV = 0
      simp only [Category.assoc]
      -- Now: ofLE ≫ (Is_to_kerZ ≫ (kerZ.arrow ≫ πV)) = 0
      -- Rewrite Is_to_kerZ ≫ kerZ.arrow = Is_to_fil (need left-association)
      conv_lhs => rw [← Category.assoc Is_to_kerZ kerZ.arrow πV,
                       h_Is_to_kerZ]
      -- Goal: ofLE(I_s1, I_s) ≫ (Is_to_fil ≫ πV) = 0
      -- Show ofLE(I_s1, I_s) ≫ Is_to_fil factors through ι_fil
      -- First, show I_s1.arrow ≫ eqToHom e_deg_inv factors through (fil(s+1,k)).arrow
      have h_I_s1_factors : (FC.fil (s + 1) k).Factors (I_s1.arrow ≫ eqToHom e_deg_inv) := by
        have h_le_s1 : I_s1 ≤ FC.fil (s + 1) (k + 1 - 1) := inf_le_right
        have h_arrow_s1 : I_s1.arrow = Subobject.ofLE I_s1 (FC.fil (s + 1) (k + 1 - 1)) h_le_s1 ≫
            (FC.fil (s + 1) (k + 1 - 1)).arrow := (Subobject.ofLE_arrow h_le_s1).symm
        rw [h_arrow_s1, Category.assoc]
        have h_transport_s1 : (FC.fil (s + 1) (k + 1 - 1)).arrow ≫ eqToHom e_deg_inv =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
              (show k + 1 - 1 = k by omega)) ≫ (FC.fil (s + 1) k).arrow := by
          have : ∀ (a b : ℤ) (h : a = b),
              (FC.fil (s + 1) a).arrow ≫ eqToHom (congr_arg FC.A h) =
              eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j)) h) ≫
              (FC.fil (s + 1) b).arrow := by
            intro a b h; subst h; simp
          exact this (k + 1 - 1) k (by omega)
        rw [h_transport_s1, ← Category.assoc]
        exact Subobject.factors_comp_arrow _
      -- Factor: I_s1.arrow ≫ eqToHom e_deg_inv = lift_s1' ≫ (fil(s+1,k)).arrow
      let lift_s1' := Subobject.factorThru (FC.fil (s + 1) k) (I_s1.arrow ≫ eqToHom e_deg_inv)
          h_I_s1_factors
      have h_lift_s1' : lift_s1' ≫ (FC.fil (s + 1) k).arrow =
          I_s1.arrow ≫ eqToHom e_deg_inv :=
        Subobject.factorThru_arrow _ _ _
      -- Show: ofLE(I_s1, I_s) ≫ Is_to_fil = lift_s1' ≫ ι_fil
      have h_ofLE_Is_to_fil :
          Subobject.ofLE I_s1 I_s hle ≫ Is_to_fil = lift_s1' ≫ ι_fil := by
        apply (cancel_mono (FC.fil s k).arrow).mp
        rw [Category.assoc, h_Is_to_fil_eq]
        rw [← Category.assoc, Subobject.ofLE_arrow hle]
        rw [Category.assoc,
          show ι_fil ≫ (FC.fil s k).arrow = (FC.fil (s + 1) k).arrow
            from Subobject.ofLE_arrow (FC.fil_anti s k)]
        exact h_lift_s1'.symm
      rw [← Category.assoc, h_ofLE_Is_to_fil, Category.assoc]
      -- Goal: lift_s1' ≫ (ι_fil ≫ πV) = 0
      rw [show ι_fil ≫ πV = 0 from cokernel.condition ι_fil, comp_zero]
    -- Inverse map gr^s H_k → E_∞
    let inv := cokernel.desc _ inv_Fs h_inv_kills_Fs1
    -- Round-trip identities
    have h_hom_inv : fwd ≫ inv = 𝟙 _ := by
      -- Goal: fwd ≫ inv = 𝟙 (cokernel (ofLE(B_⊤, Z_⊤)))
      -- fwd = cokernel.desc _ fwd_Z h_fwd_kills_B
      -- inv = cokernel.desc _ inv_Fs h_inv_kills_Fs1
      -- πLHS = cokernel.π (ofLE(B_⊤, Z_⊤))
      -- Strategy: cancel_epi πLHS, then cancel_epi e_Z, then algebraic manipulations.
      -- Step 1: It suffices to show πLHS ≫ (fwd ≫ inv) = πLHS (cancel_epi πLHS)
      apply (cancel_epi πLHS).mp
      rw [Category.comp_id]
      -- Now: πLHS ≫ (fwd ≫ inv) = πLHS
      -- πLHS ≫ fwd = fwd_Z by cokernel.π_desc
      have h_πLHS_fwd : πLHS ≫ fwd = fwd_Z := cokernel.π_desc _ _ _
      rw [← Category.assoc, h_πLHS_fwd]
      -- Now: fwd_Z ≫ inv = πLHS
      -- Step 2: cancel_epi e_Z (e_Z is epi as factorThruImageSubobject)
      apply (cancel_epi e_Z).mp
      -- Now: e_Z ≫ (fwd_Z ≫ inv) = e_Z ≫ πLHS
      rw [← Category.assoc, h_fwd_Z]
      -- Now: fwd_kerZ ≫ inv = e_Z ≫ πLHS
      -- fwd_kerZ = φ_to_Fs ≫ πRHS
      change (φ_to_Fs ≫ πRHS) ≫ inv = e_Z ≫ πLHS
      rw [Category.assoc]
      -- πRHS ≫ inv = cokernel.π _ ≫ cokernel.desc _ inv_Fs _ = inv_Fs
      have h_πRHS_inv : πRHS ≫ inv = inv_Fs := cokernel.π_desc _ _ _
      rw [h_πRHS_inv]
      -- Now: φ_to_Fs ≫ inv_Fs = e_Z ≫ πLHS
      -- Step 3: show kerZ_to_Is ≫ e_Fs = φ_to_Fs (via cancel_mono)
      have h_compat : kerZ_to_Is ≫ e_Fs = φ_to_Fs := by
        apply (cancel_mono (imageSubobject gen_s).arrow).mp
        rw [Category.assoc, imageSubobject_arrow_comp]
        -- LHS: kerZ_to_Is ≫ gen_s = φ_pre (by h_func)
        rw [h_func, h_φ_to_Fs]
      -- Step 4: φ_to_Fs ≫ inv_Fs = kerZ_to_Is ≫ e_Fs ≫ inv_Fs
      rw [← h_compat, Category.assoc, h_inv_Fs]
      -- Now: kerZ_to_Is ≫ inv_Is = e_Z ≫ πLHS
      -- inv_Is = Is_to_kerZ ≫ e_Z ≫ πLHS
      change kerZ_to_Is ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = e_Z ≫ πLHS
      -- Step 5: show kerZ_to_Is ≫ Is_to_kerZ = 𝟙
      have h_round : kerZ_to_Is ≫ Is_to_kerZ = 𝟙 _ := by
        -- Use cancel_mono kerZ.arrow
        apply (cancel_mono kerZ.arrow).mp
        rw [Category.id_comp, Category.assoc, h_Is_to_kerZ]
        -- Now: kerZ_to_Is ≫ Is_to_fil = kerZ.arrow
        -- Use cancel_mono (FC.fil s k).arrow
        apply (cancel_mono (FC.fil s k).arrow).mp
        rw [Category.assoc, h_Is_to_fil_eq]
        -- Now: kerZ_to_Is ≫ I_s.arrow ≫ eqToHom e_deg_inv = kerZ.arrow ≫ (FC.fil s k).arrow
        rw [← Category.assoc, h_kerZ_to_Is]
        -- Now: φ_to_X2 ≫ eqToHom e_deg_inv = kerZ.arrow ≫ (FC.fil s k).arrow
        -- φ_to_X2 = kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg
        change (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) ≫ eqToHom e_deg_inv =
          kerZ.arrow ≫ (FC.fil s k).arrow
        rw [Category.assoc, Category.assoc]
        congr 1
        -- eqToHom e_deg ≫ eqToHom e_deg_inv = 𝟙
        simp [eqToHom_trans]
      rw [← Category.assoc, ← Category.assoc, h_round, Category.id_comp]
    have h_inv_hom : inv ≫ fwd = 𝟙 _ := by
      -- Goal: inv ≫ fwd = 𝟙 (cokernel (ofLE(F_{s+1}, F_s)))
      -- Strategy: cancel_epi πRHS, then cancel_epi e_Fs, then algebraic manipulations.
      -- Step 1: cancel_epi πRHS
      apply (cancel_epi πRHS).mp
      rw [Category.comp_id, ← Category.assoc]
      -- Goal: (πRHS ≫ inv) ≫ fwd = πRHS
      have h_πRHS_inv' : πRHS ≫ inv = inv_Fs := cokernel.π_desc _ _ _
      rw [h_πRHS_inv']
      -- Now: inv_Fs ≫ fwd = πRHS
      -- Step 2: cancel_epi e_Fs
      apply (cancel_epi e_Fs).mp
      rw [← Category.assoc, h_inv_Fs]
      -- Now: inv_Is ≫ fwd = e_Fs ≫ πRHS
      -- inv_Is = Is_to_kerZ ≫ e_Z ≫ πLHS
      change (Is_to_kerZ ≫ e_Z ≫ πLHS) ≫ fwd = e_Fs ≫ πRHS
      rw [Category.assoc, Category.assoc]
      have h_πLHS_fwd' : πLHS ≫ fwd = fwd_Z := cokernel.π_desc _ _ _
      rw [h_πLHS_fwd', h_fwd_Z]
      -- Now: Is_to_kerZ ≫ (φ_to_Fs ≫ πRHS) = e_Fs ≫ πRHS
      change Is_to_kerZ ≫ (φ_to_Fs ≫ πRHS) = e_Fs ≫ πRHS
      rw [← Category.assoc]
      -- Now: (Is_to_kerZ ≫ φ_to_Fs) ≫ πRHS = e_Fs ≫ πRHS
      congr 1
      -- Step 3: show Is_to_kerZ ≫ φ_to_Fs = e_Fs
      apply (cancel_mono (imageSubobject gen_s).arrow).mp
      rw [Category.assoc, h_φ_to_Fs, imageSubobject_arrow_comp]
      -- Now: Is_to_kerZ ≫ φ_pre = gen_s
      change Is_to_kerZ ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ) =
        S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ
      rw [← Category.assoc]
      congr 1
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.liftCycles_i, S.liftCycles_i]
      -- Now: Is_to_kerZ ≫ φ_to_X2 = I_s.arrow
      change Is_to_kerZ ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) = I_s.arrow
      rw [show Is_to_kerZ ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
          (Is_to_kerZ ≫ kerZ.arrow) ≫ (FC.fil s k).arrow ≫ eqToHom e_deg by
        simp only [Category.assoc]]
      rw [h_Is_to_kerZ, show Is_to_fil ≫ (FC.fil s k).arrow ≫ eqToHom e_deg =
          (Is_to_fil ≫ (FC.fil s k).arrow) ≫ eqToHom e_deg by rw [Category.assoc]]
      rw [h_Is_to_fil_eq, Category.assoc]
      -- Now: I_s.arrow ≫ eqToHom e_deg_inv ≫ eqToHom e_deg = I_s.arrow
      simp [eqToHom_trans]
    exact ⟨fwd, inv, h_hom_inv, h_inv_hom⟩

end KIP126.Core.SpectralSequence
