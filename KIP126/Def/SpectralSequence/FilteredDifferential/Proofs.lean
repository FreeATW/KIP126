import Mathlib.CategoryTheory.Abelian.Exact
import KIP126.Def.SpectralSequence.FilteredDifferential.Data
import KIP126.Def.SpectralSequence.FilteredPage.Proofs

/-! # Square-zero and cycle-kernel laws for the filtered-page differential -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem pageDifferential_comp (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    FC.pageDifferential s k n ≫ FC.pageDifferential (s + ↑n) (k - 1) n = 0 := by
  set f₁ := Subobject.ofLE (FC.boundarySubobject s k ↑n) (FC.cycleSubobject s k ↑n)
    (FC.B_le_Z_aux s k ↑n)
  haveI : Epi (cokernel.π f₁) := inferInstance
  rw [show FC.pageDifferential s k n ≫ FC.pageDifferential (s + ↑n) (k - 1) n =
    FC.pageDifferential s k n ≫ FC.pageDifferential (s + ↑n) (k - 1) n from rfl]
  rw [← cancel_epi (cokernel.π f₁), comp_zero, ← Category.assoc]
  erw [cokernel.π_desc]
  set f_n₁ := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫ cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
  set kerZ₁ := kernelSubobject f_n₁
  set ι₁ := Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k)
  set πV₁ := cokernel.π ι₁
  set p₁ := factorThruImageSubobject (kerZ₁.arrow ≫ πV₁)
  haveI : Epi p₁ := inferInstance
  rw [← cancel_epi p₁, comp_zero, ← Category.assoc]
  erw [Abelian.comp_epiDesc]
  rw [Category.assoc]
  erw [cokernel.π_desc]
  rw [Category.assoc]
  erw [Abelian.comp_epiDesc]
  simp only [Category.assoc]
  erw [show ∀ {A' B' C' D' : C} (f : A' ⟶ B') (g : B' ⟶ C') (h : C' ⟶ D'),
    f ≫ (g ≫ h) = (f ≫ g) ≫ h from fun f g h => (Category.assoc f g h).symm]
  suffices h_zero : _ ≫ _ = (0 : _ ⟶ Subobject.underlying.obj (kernelSubobject
    ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow ≫ FC.complex.d (k - 1 - 1) (k - 1 - 1 - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n + ↑n + ↑n) (k - 1 - 1 - 1)).arrow)))) by
    erw [h_zero, zero_comp]
  apply (inferInstance : Mono (kernelSubobject
    ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow ≫ FC.complex.d (k - 1 - 1) (k - 1 - 1 - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n + ↑n + ↑n) (k - 1 - 1 - 1)).arrow))).arrow).right_cancellation
  simp only [zero_comp, Category.assoc]
  erw [factorThruKernelSubobject_comp_arrow]
  apply (inferInstance : Mono (FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow).right_cancellation
  simp only [zero_comp, Category.assoc]
  erw [Abelian.monoLift_comp]
  conv_lhs => erw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
  conv_lhs => erw [← Category.assoc, Abelian.monoLift_comp]
  erw [Category.assoc, Category.assoc, FC.complex.d_comp_d k, comp_zero, comp_zero]




private theorem kernelSubobject_epiDesc' {C' : Type*} [Category C'] [Abelian C']
    {A' B' D' : C'} (p : A' ⟶ B') [Epi p] (g : A' ⟶ D')
    (hg : kernel.ι p ≫ g = 0) :
    kernelSubobject (Abelian.epiDesc p g hg) =
      imageSubobject ((kernelSubobject g).arrow ≫ p) := by
  apply le_antisymm
  · -- (≤): ker(epiDesc) ≤ image((ker g).arrow ≫ p)
    set K := kernelSubobject (Abelian.epiDesc p g hg) with hK_def
    -- Form the pullback of p (epi) and K.arrow (mono)
    have hpb_comm : pullback.fst p K.arrow ≫ p = pullback.snd p K.arrow ≫ K.arrow :=
      pullback.condition
    haveI : Mono (pullback.fst p K.arrow) :=
      pullback.fst_of_mono (f := p) (g := K.arrow)
    haveI : Epi (pullback.snd p K.arrow) :=
      Abelian.epi_pullback_of_epi_f p K.arrow
    -- Show pullback.fst ≫ g = 0
    have h_fst_g_zero : pullback.fst p K.arrow ≫ g = 0 := by
      calc pullback.fst p K.arrow ≫ g
          = pullback.fst p K.arrow ≫ (p ≫ Abelian.epiDesc p g hg) :=
            by rw [Abelian.comp_epiDesc]
        _ = (pullback.fst p K.arrow ≫ p) ≫ Abelian.epiDesc p g hg :=
            (Category.assoc _ _ _).symm
        _ = (pullback.snd p K.arrow ≫ K.arrow) ≫ Abelian.epiDesc p g hg :=
            by rw [hpb_comm]
        _ = pullback.snd p K.arrow ≫ (K.arrow ≫ Abelian.epiDesc p g hg) :=
            Category.assoc _ _ _
        _ = pullback.snd p K.arrow ≫ 0 := by rw [kernelSubobject_arrow_comp]
        _ = 0 := comp_zero
    -- Factor through ker(g)
    set φ := factorThruKernelSubobject g (pullback.fst p K.arrow) h_fst_g_zero
    have hφ_spec : φ ≫ (kernelSubobject g).arrow = pullback.fst p K.arrow :=
      factorThruKernelSubobject_comp_arrow g _ _
    -- Key equation: φ ≫ ker(g).arrow ≫ p = pullback.snd ≫ K.arrow
    have h_key_eq : φ ≫ (kernelSubobject g).arrow ≫ p =
        pullback.snd p K.arrow ≫ K.arrow := by
      rw [show φ ≫ (kernelSubobject g).arrow ≫ p =
        (φ ≫ (kernelSubobject g).arrow) ≫ p from (Category.assoc _ _ _).symm,
        hφ_spec, hpb_comm]
    -- image(pullback.snd ≫ K.arrow) = K (since snd is epi, K.arrow is mono)
    have h_img_epi_comp : ∀ {X₁ X₂ X₃ : C'} (e : X₁ ⟶ X₂) [Epi e] (h : X₂ ⟶ X₃),
        imageSubobject (e ≫ h) = imageSubobject h := by
      intro X₁ X₂ X₃ e _ h
      have hle := imageSubobject_comp_le e h
      haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e h
      haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
      exact le_antisymm hle (Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
        (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm))
    have h_img_epi : imageSubobject (pullback.snd p K.arrow ≫ K.arrow) = K := by
      rw [h_img_epi_comp, imageSubobject_mono, Subobject.mk_arrow]
    calc K = imageSubobject (pullback.snd p K.arrow ≫ K.arrow) := h_img_epi.symm
      _ = imageSubobject (φ ≫ (kernelSubobject g).arrow ≫ p) := by rw [h_key_eq]
      _ ≤ imageSubobject ((kernelSubobject g).arrow ≫ p) :=
            imageSubobject_comp_le φ ((kernelSubobject g).arrow ≫ p)
  · -- (≥): image((ker g).arrow ≫ p) ≤ ker(epiDesc)
    apply le_kernelSubobject
    rw [← cancel_epi (factorThruImageSubobject ((kernelSubobject g).arrow ≫ p)),
        comp_zero, ← Category.assoc,
        imageSubobject_arrow_comp ((kernelSubobject g).arrow ≫ p),
        Category.assoc, Abelian.comp_epiDesc, kernelSubobject_arrow_comp]

-- Heavy unification through cokernel desc and kernel subobject factoring


private theorem kernelSubobject_cokernel_desc' {C' : Type*} [Category C'] [Abelian C']
    {A' B' D' : C'} (f : A' ⟶ B') (g : B' ⟶ D') (w : f ≫ g = 0) :
    kernelSubobject (cokernel.desc f g w) =
      imageSubobject ((kernelSubobject g).arrow ≫ cokernel.π f) := by
  apply le_antisymm
  · -- (≤): ker(desc) ≤ image(ker(g).arrow ≫ cokernel.π f)
    -- Pullback argument: pull back π (epi) along K.arrow (mono) where K = ker(desc).
    -- The pullback P has:
    --   pullback.fst : P → B' (mono, since K.arrow is mono)
    --   pullback.snd : P → K (epi, since π is epi)
    -- Then fst ≫ g = fst ≫ π ≫ desc = snd ≫ K.arrow ≫ desc = 0,
    -- so fst factors through ker(g). This shows image(ker(g).arrow ≫ π) ⊇ K.
    set K := kernelSubobject (cokernel.desc f g w) with hK_def
    set π := cokernel.π f with hπ_def
    set desc' := cokernel.desc f g w with hdesc'_def
    -- Form the pullback of π and K.arrow
    have hpb_comm : pullback.fst π K.arrow ≫ π = pullback.snd π K.arrow ≫ K.arrow :=
      pullback.condition
    -- pullback.fst is mono (since K.arrow is mono)
    haveI : Mono (pullback.fst π K.arrow) :=
      pullback.fst_of_mono (f := π) (g := K.arrow)
    -- pullback.snd is epi (since π is epi, in abelian category)
    haveI : Epi (pullback.snd π K.arrow) :=
      Abelian.epi_pullback_of_epi_f π K.arrow
    -- Show pullback.fst ≫ g = 0, so it factors through ker(g)
    have h_fst_g_zero : pullback.fst π K.arrow ≫ g = 0 := by
      calc pullback.fst π K.arrow ≫ g
          = pullback.fst π K.arrow ≫ (π ≫ desc') := by rw [hπ_def, cokernel.π_desc]
        _ = (pullback.fst π K.arrow ≫ π) ≫ desc' := (Category.assoc _ _ _).symm
        _ = (pullback.snd π K.arrow ≫ K.arrow) ≫ desc' := by rw [hpb_comm]
        _ = pullback.snd π K.arrow ≫ (K.arrow ≫ desc') := Category.assoc _ _ _
        _ = pullback.snd π K.arrow ≫ 0 := by rw [kernelSubobject_arrow_comp]
        _ = 0 := comp_zero
    -- Factor through ker(g)
    set φ := factorThruKernelSubobject g (pullback.fst π K.arrow) h_fst_g_zero
    have hφ_spec : φ ≫ (kernelSubobject g).arrow = pullback.fst π K.arrow :=
      factorThruKernelSubobject_comp_arrow g _ _
    -- Key equation: φ ≫ ker(g).arrow ≫ π = pullback.snd ≫ K.arrow
    have h_key_eq : φ ≫ (kernelSubobject g).arrow ≫ π = pullback.snd π K.arrow ≫ K.arrow := by
      rw [show φ ≫ (kernelSubobject g).arrow ≫ π =
        (φ ≫ (kernelSubobject g).arrow) ≫ π from (Category.assoc _ _ _).symm,
        hφ_spec, hpb_comm]
    -- Now: image(pullback.snd ≫ K.arrow) = image(K.arrow) since pullback.snd is epi
    -- Use: imageSubobject(e ≫ m) = imageSubobject(m) when e is epi
    -- (inline proof since the helper in Basic.lean is private)
    have h_img_epi_comp : ∀ {X₁ X₂ X₃ : C'} (e : X₁ ⟶ X₂) [Epi e] (h : X₂ ⟶ X₃),
        imageSubobject (e ≫ h) = imageSubobject h := by
      intro X₁ X₂ X₃ e _ h
      have hle := imageSubobject_comp_le e h
      haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e h
      haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
      exact le_antisymm hle (Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
        (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm))
    have h_img_epi : imageSubobject (pullback.snd π K.arrow ≫ K.arrow) = K := by
      rw [h_img_epi_comp, imageSubobject_mono, Subobject.mk_arrow]
    -- Rewrite: image(φ ≫ ker(g).arrow ≫ π) = image(pullback.snd ≫ K.arrow) = K
    -- And: image(φ ≫ ker(g).arrow ≫ π) ≤ image(ker(g).arrow ≫ π) by imageSubobject_comp_le
    calc K = imageSubobject (pullback.snd π K.arrow ≫ K.arrow) := h_img_epi.symm
      _ = imageSubobject (φ ≫ (kernelSubobject g).arrow ≫ π) := by rw [h_key_eq]
      _ ≤ imageSubobject ((kernelSubobject g).arrow ≫ π) :=
            imageSubobject_comp_le φ ((kernelSubobject g).arrow ≫ π)
  · -- (≥): image(ker(g).arrow ≫ cokernel.π f) ≤ ker(desc)
    apply le_kernelSubobject
    rw [← cancel_epi (factorThruImageSubobject ((kernelSubobject g).arrow ≫ cokernel.π f)),
        comp_zero, ← Category.assoc,
        imageSubobject_arrow_comp ((kernelSubobject g).arrow ≫ cokernel.π f),
        Category.assoc, cokernel.π_desc, kernelSubobject_arrow_comp]



set_option backward.isDefEq.respectTransparency false in
-- Multi-step proof: Z_{n+1} ↪ Z_n maps to kernel of page differential via index shifting
/-- The ≥ direction of Z_succ: image(ofLE(Z_{n+1}, Z_n) ≫ pageπ n) ≤ kernel(pageDifferential).
    Elements of Z_{n+1} (deeper cycle condition: dx ∈ F^{s+n+1}) map to zero under pageDiff
    because their d-image lands in F^{s+n+1}, hence projects to 0 in gr^{s+n}. -/
theorem pageDifferential_Z_succ_ge (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    imageSubobject (
      Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1)) (FC.cycleSubobject s k ↑n)
        (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
      FC.pageπ s k ↑n) ≤
    kernelSubobject (FC.pageDifferential s k n) := by
  -- It suffices to show: ofLE(Z_{n+1}, Z_n) ≫ pageπ n ≫ pageDiff = 0
  -- Then the imageSubobject of (ofLE ≫ pageπ) has arrow killing pageDiff.
  apply le_kernelSubobject
  -- Goal: (imageSubobject(ofLE ≫ pageπ)).arrow ≫ pageDiff = 0
  -- Factor: imageSubobject(f).arrow = factorThruImage(f)⁻¹ (not quite)
  -- Use: factorThruImage(f) is epi and factorThruImage(f) ≫ imageSubobject(f).arrow = f.
  -- So imageSubobject(f).arrow ≫ g = 0 ↔ (cancel epi factorThruImage(f)) f ≫ g = 0.
  set ofLE_pageπ := Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
    (FC.cycleSubobject s k ↑n)
    (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
    FC.pageπ s k ↑n with h_ofLE_pageπ
  rw [← cancel_epi (factorThruImageSubobject ofLE_pageπ), comp_zero,
    ← Category.assoc, imageSubobject_arrow_comp]
  -- Goal: ofLE_pageπ ≫ pageDiff = 0
  -- = ofLE(Z_{n+1}, Z_n) ≫ pageπ n ≫ pageDiff = 0
  rw [h_ofLE_pageπ, Category.assoc]
  -- Use: pageπ n ≫ pageDiff = h_on_Zn (definitionally, since pageDiff = cokernel.desc _ h_on_Zn _)
  erw [cokernel.π_desc]
  -- Goal: ofLE(Z_{n+1}, Z_n) ≫ h_on_Zn = 0
  -- h_on_Zn = Abelian.epiDesc(p, ψ, _). Cancel epi p1 on the left.
  set f_n := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
  set kerZ := kernelSubobject f_n
  set ι_s := Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k)
  set πV := FC.filtration.toAssociatedGraded s k
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV)
  haveI : Epi p := inferInstance
  set f_n1 := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow)
  set kerZ1 := kernelSubobject f_n1
  set p1 := factorThruImageSubobject (kerZ1.arrow ≫ πV)
  haveI : Epi p1 := inferInstance
  rw [← cancel_epi p1, comp_zero]
  -- Goal: p1 ≫ ofLE(Z_{n+1}, Z_n) ≫ h_on_Zn = 0
  -- Key identity: p1 ≫ ofLE(Z_{n+1}, Z_n) = β ≫ p where β = ofLE(kerZ1, kerZ)
  have hkerZ1_le : kerZ1 ≤ kerZ := by
    apply le_kernelSubobject
    have hfil : FC.filtration.F (s + ↑(n + 1)) (k - 1) ≤ FC.filtration.F (s + ↑n) (k - 1) :=
      FC.filtration.le_of_le (by omega) (k - 1)
    -- kerZ1.arrow ≫ f_n = (kerZ1.arrow ≫ F^s.arrow ≫ d k) ≫ cokernel.π(F^{s+n}.arrow)
    -- kerZ1 kills f_n1, so d-image ∈ F^{s+n+1} ≤ F^{s+n}, hence ≫ cokernel.π(F^{s+n}) = 0
    have h1 : kerZ1.arrow ≫ f_n1 = 0 := kernelSubobject_arrow_comp f_n1
    -- d-image of kerZ1 factors through F^{s+n+1}
    have h1' : (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      simp only [Category.assoc] at h1 ⊢; exact h1
    set dk_im := kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)
    set lift1 := Abelian.monoLift (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow dk_im h1'
    calc kerZ1.arrow ≫ f_n
        = dk_im ≫ cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          simp only [f_n, dk_im, Category.assoc]
      _ = (lift1 ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          rw [Abelian.monoLift_comp]
      _ = lift1 ≫ (Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          rw [show (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow =
            Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow
            from (Subobject.ofLE_arrow hfil).symm]; simp only [Category.assoc]
      _ = 0 := by
          simp only [Category.assoc, cokernel.condition, comp_zero]
  set β := Subobject.ofLE kerZ1 kerZ hkerZ1_le
  -- Prove p1 ≫ ofLE(Z_{n+1}, Z_n) = β ≫ p by mono-cancellation on Z_n.arrow
  have h_factor : p1 ≫ Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
      (FC.cycleSubobject s k ↑n)
      (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) = β ≫ p := by
    apply (inferInstance : Mono (FC.cycleSubobject s k ↑n).arrow).right_cancellation
    simp only [Category.assoc]
    -- LHS: p1 ≫ ofLE(Z_{n+1}, Z_n) ≫ Z_n.arrow = p1 ≫ Z_{n+1}.arrow = kerZ1.arrow ≫ πV
    -- RHS: β ≫ p ≫ Z_n.arrow = β ≫ kerZ.arrow ≫ πV = kerZ1.arrow ≫ πV
    -- Unfold set-names and use imageSubobject_arrow_comp + ofLE_arrow
    simp only [p1, p, β]
    rw [Subobject.ofLE_arrow]
    erw [imageSubobject_arrow_comp, imageSubobject_arrow_comp]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  -- Now use h_factor: p1 ≫ ofLE = β ≫ p to rewrite
  -- Need reassociated form since the target is fully right-associated
  -- h_factor_assoc: p1 ≫ ofLE ≫ X = β ≫ p ≫ X for any X
  rw [show p1 ≫ _ = (p1 ≫ _) ≫ _ from (Category.assoc _ _ _).symm]
  rw [h_factor]
  rw [Category.assoc]
  -- Goal: β ≫ (p ≫ h_on_Zn) = 0
  -- p ≫ h_on_Zn = ψ (by Abelian.comp_epiDesc)
  -- Don't use erw [Abelian.comp_epiDesc] - erw corrupts internal terms.
  -- Use rw which preserves term structure:
  rw [Abelian.comp_epiDesc]
  -- Goal: β ≫ ψ = 0 where ψ = (to_Z_n_t) ≫ pageπ'
  set ι_t := Subobject.ofLE (FC.filtration.F (s + ↑n + 1) (k - 1)) (FC.filtration.F (s + ↑n) (k - 1))
    (FC.filtration.decreasing (s + ↑n) (k - 1))
  set πV' := FC.filtration.toAssociatedGraded (s + ↑n) (k - 1)
  -- Suffices: β ≫ to_Z_n_t = 0, then β ≫ ψ = (β ≫ to_Z_n_t) ≫ pageπ' = 0 ≫ pageπ' = 0
  suffices h : β ≫ _ = (0 : _ ⟶ Subobject.underlying.obj
    (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)) by
    rw [show β ≫ (_ ≫ _) = (β ≫ _) ≫ _ from (Category.assoc β _ _).symm]
    rw [h, zero_comp]
  -- Now: β ≫ to_Z_n_t = 0
  apply (inferInstance : Mono (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow).right_cancellation
  rw [zero_comp]
  -- Goal: β ≫ to_Z_n_t ≫ cycleSubobject.arrow = 0
  simp only [Category.assoc]
  unfold FilteredComplex.cycleSubobject
  push_cast
  simp only [imageSubobject_arrow_comp]
  -- factorThruKernelSubobject_comp_arrow fails due to erw pollution from cokernel.π_desc.
  -- The factorThruKernelSubobject and kernelSubobject have the same 'f' in the pretty-printer
  -- but differ internally. Work around by using the unfold approach:
  simp only [factorThruKernelSubobject]
  -- Goal: β ≫ factorThru(P, monoLift, w) ≫ P.arrow ≫ πV' = 0
  -- P = kernelSubobject(f') but the P in factorThru and P in arrow may differ internally.
  -- Since the type of factorThru ≫ arrow typechecks, they share the same underlying obj.
  -- Use Subobject.factorThru_arrow as a have:
  set f' := (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) with hf'_def
  set ml := Abelian.monoLift (FC.filtration.F (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))
    (by simp only [Category.assoc]; exact kernelSubobject_arrow_comp f_n) with hml_def
  -- Now β ≫ factorThru(kerSub f', ml, _) ≫ (kerSub f').arrow ≫ πV' = 0
  -- factorThru_arrow: factorThru(kerSub f', ml, _) ≫ (kerSub f').arrow = ml
  -- Try rw with the explicit f':
  -- NOTE: The goal after push_cast + simp [imageSubobject_arrow_comp] is:
  -- β ≫ factorThru(P, ml, w) ≫ P'.arrow ≫ πV' = 0
  -- where P and P' are propositionally equal kernelSubobject instances that differ
  -- internally due to erw [cokernel.π_desc] pollution.
  -- factorThru_arrow cannot be applied by rw/simp/erw because the subobjects don't match.
  -- The mathematical proof: β ≫ ml ≫ πV' = 0 because β ≫ ml factors through
  -- F^{s+n+1} ≤ F^{s+n} and ofLE(F^{s+n+1}, F^{s+n}) ≫ πV' = 0 (cokernel condition).
  -- The goal is:
  -- β ≫ (kernelSubobject f'_expr).factorThru (monoLift ...) ⋯ ≫
  --     (kernelSubobject f'_expr).arrow ≫ πV' = 0
  -- Both kernelSubobject instances use the same f' expression.
  -- factorThru_arrow: P.factorThru h w ≫ P.arrow = h
  -- Try slice_lhs to isolate factorThru ≫ arrow
  -- The goal is β ≫ P.factorThru(ml, w) ≫ P.arrow ≫ πV' = 0
  -- where P = kernelSubobject f'. But erw/rw can't match factorThru_arrow.
  -- Use have + Mono.right_cancellation on P.arrow to replace factorThru with ml.
  -- Actually: P.factorThru(ml, w) is the unique map through P such that
  -- P.factorThru(ml, w) ≫ P.arrow = ml. This holds by factorThru_arrow.
  -- But the P in factorThru and P in .arrow must be the same for this to work.
  -- Since they print the same but erw can't match, they differ in proof terms.
  -- New approach: show the goal by converting to a statement about `ml ≫ πV'` directly.
  -- Use have : P.factorThru(ml, w) ≫ P.arrow = ml for the P that factorThru uses.
  -- Step 1: Extract the factorThru subobject using set
  -- The P in factorThru and P in .arrow differ internally (erw pollution)
  -- but both kernelSubobjects are for the same morphism, so they're propositionally equal.
  -- The goal is: β ≫ P.factorThru(ml, w) ≫ P'.arrow ≫ πV' = 0
  -- Strategy: show it's equal to β ≫ ml ≫ πV' = 0, then prove the latter.
  -- Use `convert` to match against β ≫ ml ≫ πV' = 0.
  suffices h_main : β ≫ ml ≫ πV' = 0 by
    convert h_main using 2 <;> try rfl
    -- Goal: P.factorThru(ml_expr, w) ≫ P.arrow ≫ πV' = ml ≫ πV'
    rw [show (_ : Subobject.underlying.obj _ ⟶ _) ≫ _ ≫ πV' = (_ ≫ _) ≫ πV'
      from (Category.assoc _ _ _).symm, Subobject.factorThru_arrow]
  -- Now: β ≫ ml ≫ πV' = 0
  -- Strategy: β ≫ ml ≫ F^{s+n}.arrow = kerZ1.arrow ≫ F^s.arrow ≫ d(k)
  -- which factors through F^{s+n+1}(k-1), and then ≫ πV' = 0 by cokernel.condition.
  -- Avoid problematic rw by using Mono.right_cancellation and calc chains.
  --
  -- Step 1: kerZ1.arrow ≫ F^s.arrow ≫ d(k) factors through F^{s+↑(n+1)}(k-1)
  have h_kerZ1_factor : (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
      cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc]
    exact kernelSubobject_arrow_comp f_n1
  set lift_n1 := Abelian.monoLift (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow
    (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) h_kerZ1_factor
  have h_lift_n1_spec : lift_n1 ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow =
      kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) :=
    Abelian.monoLift_comp _ _ _
  -- Step 2: β ≫ ml ≫ F^{s+n}.arrow = lift_n1 ≫ F^{s+↑(n+1)}.arrow
  have hfil_le_nat : FC.filtration.F (s + ↑(n + 1)) (k - 1) ≤ FC.filtration.F (s + ↑n) (k - 1) :=
    FC.filtration.le_of_le (by omega) (k - 1)
  -- Both sides equal kerZ1.arrow ≫ F^s.arrow ≫ d(k)
  -- Use Mono.right_cancellation on F^{s+n}.arrow to get β ≫ ml = lift_n1 ≫ ofLE
  have h_β_ml_eq : β ≫ ml = lift_n1 ≫ Subobject.ofLE _ _ hfil_le_nat := by
    apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
    -- LHS: β ≫ ml ≫ F^{s+n}.arrow
    -- RHS: lift_n1 ≫ ofLE ≫ F^{s+n}.arrow = lift_n1 ≫ F^{s+↑(n+1)}.arrow
    -- Both = kerZ1.arrow ≫ F^s.arrow ≫ d(k)
    -- Compute LHS via monoLift_comp + ofLE_arrow:
    --   β ≫ ml ≫ F^{s+n}.arrow
    --   = β ≫ (kerZ.arrow ≫ F^s.arrow ≫ d(k))    [ml_def + monoLift_comp]
    --   = (β ≫ kerZ.arrow) ≫ F^s.arrow ≫ d(k)    [assoc]
    --   = kerZ1.arrow ≫ F^s.arrow ≫ d(k)           [ofLE_arrow]
    -- Compute RHS:
    --   lift_n1 ≫ ofLE ≫ F^{s+n}.arrow
    --   = lift_n1 ≫ F^{s+↑(n+1)}.arrow             [ofLE_arrow]
    --   = kerZ1.arrow ≫ F^s.arrow ≫ d(k)           [lift_n1_spec]
    -- Instead of rw which may fail due to pollution, use calc:
    have h_ml_arrow : ml ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
        kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
      simp only [hml_def]; exact Abelian.monoLift_comp _ _ _
    calc (β ≫ ml) ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow
        = β ≫ (ml ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) := Category.assoc _ _ _
      _ = β ≫ (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) := by rw [h_ml_arrow]
      _ = (β ≫ kerZ.arrow) ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
          simp only [Category.assoc]
      _ = kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
          rw [Subobject.ofLE_arrow hkerZ1_le]
      _ = lift_n1 ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow := h_lift_n1_spec.symm
      _ = lift_n1 ≫ (Subobject.ofLE _ _ hfil_le_nat ≫
            (FC.filtration.F (s + ↑n) (k - 1)).arrow) := by rw [Subobject.ofLE_arrow]
      _ = (lift_n1 ≫ Subobject.ofLE _ _ hfil_le_nat) ≫
            (FC.filtration.F (s + ↑n) (k - 1)).arrow := (Category.assoc _ _ _).symm
  -- Step 3: (β ≫ ml) ≫ πV' = (lift_n1 ≫ ofLE) ≫ πV' = lift_n1 ≫ ofLE ≫ πV'
  -- and ofLE ≫ πV' = 0 because πV' = cokernel.π(ι_t) and ofLE ≫ F^{s+n}.arrow = ι_t ≫ F^{s+n}.arrow
  -- More directly: Subobject.ofLE(F^{s+↑(n+1)}, F^{s+n}) ≫ πV' = 0
  -- because πV' = cokernel.π of the inclusion of F^{s+↑n+1} into F^{s+n}
  -- and ofLE factors through that inclusion.
  rw [show β ≫ ml ≫ πV' = (β ≫ ml) ≫ πV' from (Category.assoc _ _ _).symm,
    h_β_ml_eq, Category.assoc]
  -- Goal: lift_n1 ≫ Subobject.ofLE(F^{s+↑(n+1)}, F^{s+n}) ≫ πV' = 0
  -- s + ↑(n+1) = s + ↑n + 1, so ofLE factors through ι_t and cokernel kills it.
  suffices h_zero : Subobject.ofLE _ _ hfil_le_nat ≫ πV' = 0 by
    rw [h_zero, comp_zero]
  -- Identify the two equal integer indices through an isomorphism of subobjects.
  -- This avoids rewriting dependent cokernels across `↑(n + 1) = ↑n + 1`.
  have h_idx_eq : (s : ℤ) + ↑(n + 1) = s + ↑n + 1 := by omega
  have h_fil_eq : FC.filtration.F (s + ↑(n + 1)) (k - 1) =
      FC.filtration.F (s + ↑n + 1) (k - 1) := by
    rw [h_idx_eq]
  have h_factor : Subobject.ofLE _ _ hfil_le_nat =
      (Subobject.isoOfEq (FC.filtration.F (s + ↑(n + 1)) (k - 1))
        (FC.filtration.F (s + ↑n + 1) (k - 1)) h_fil_eq).hom ≫ ι_t := by
    apply (cancel_mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).mp
    simp only [Category.assoc, Subobject.isoOfEq_hom, ι_t,
      Subobject.ofLE_arrow]
  rw [h_factor, Category.assoc]
  dsimp [πV']
  unfold KIP126.Core.Algebra.Filtration.toAssociatedGraded
    KIP126.Core.Algebra.Filtration.associatedGraded
  rw [cokernel.condition, comp_zero]


private theorem eqToHom_arrow_dToK_gen_local (FC : FilteredComplex C)
    (s : ℤ) (m k : ℤ) (hmk : m + 1 = k) :
    eqToHom (show Subobject.underlying.obj (FC.filtration.F s k) =
      Subobject.underlying.obj (FC.filtration.F s (m + 1)) by rw [hmk]) ≫
    ((FC.filtration.F s (m + 1)).arrow ≫ FC.dToK m) =
      (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      eqToHom (congr_arg FC.complex.X (show k - 1 = m by omega)) := by
  subst hmk
  simp [FilteredComplex.dToK]

private theorem eqToHom_arrow_dToK_local (FC : FilteredComplex C)
    (s k : ℤ) :
    eqToHom (show Subobject.underlying.obj (FC.filtration.F s k) =
      Subobject.underlying.obj (FC.filtration.F s ((k - 1) + 1)) by
      rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
    ((FC.filtration.F s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
      (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
  rw [eqToHom_arrow_dToK_gen_local FC s (k - 1) k (by omega)]
  simp

private lemma imageSubobject_epi_comp'_local {C' : Type*} [Category C'] [Abelian C']
    {X₁ X₂ X₃ : C'} (e : X₁ ⟶ X₂) [Epi e] (f : X₂ ⟶ X₃) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
    (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm)

set_option maxHeartbeats 6400000 in
/-- Every class in the kernel of the finite-page differential has a representative
in the next cycle subobject. Adapted from the filtered-complex proof in KIPBase. -/
theorem pageDifferential_Z_succ_le (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    kernelSubobject (FC.pageDifferential s k n) ≤
    imageSubobject (
      Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1)) (FC.cycleSubobject s k ↑n)
        (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
      FC.pageπ s k ↑n) := by
  -- Reconstruct the internal abbreviations of pageDifferential
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
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV) with hp_def
  haveI hp_epi : Epi p := inferInstance
  -- Reconstruct lift_n, lift_to_kerZ', to_Z_n_t, ψ
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
  set pageπ_t := FC.pageπ (s + ↑n) (k - 1) ↑n with hpageπ_t_def
  set ψ := to_Z_n_t ≫ pageπ_t with hψ_def
  -- Phase A: Establish kernelSubobject(pageDiff) = imageSubobject((ker ψ).arrow ≫ p ≫ pageπ)
  -- Use erw in a have block to contain the pollution
  have h_ker_le : kernelSubobject (FC.pageDifferential s k n) ≤
      imageSubobject ((kernelSubobject ψ).arrow ≫ p ≫ FC.pageπ s k ↑n) := by
    erw [kernelSubobject_cokernel_desc']
    erw [kernelSubobject_epiDesc']
    -- The epi image factorization identifies the two iterated images.
    erw [← imageSubobject_epi_comp'_local
      (factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p))
      ((imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow ≫
        FC.pageπ s k ↑n)]
    -- Goal: imageSubobject(factorThru ≫ img.arrow ≫ pageπ) ≤ imageSubobject(f ≫ pageπ)
    -- factorThru ≫ img.arrow ≫ pageπ is parsed as factorThru ≫ (img.arrow ≫ pageπ)
    -- We need: factorThru ≫ (img.arrow ≫ pageπ) = (factorThru ≫ img.arrow) ≫ pageπ = f ≫ pageπ
    erw [show factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p) ≫
      (imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow ≫
      FC.pageπ s k ↑n =
      (factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p) ≫
      (imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow) ≫
      FC.pageπ s k ↑n from (Category.assoc _ _ _).symm,
      imageSubobject_arrow_comp ((kernelSubobject ψ).arrow ≫ p),
      Category.assoc]
  -- Phase B: Show imageSubobject((ker ψ).arrow ≫ p ≫ pageπ) ≤ imageSubobject(ofLE ≫ pageπ)
  apply le_trans h_ker_le
  -- Goal: imageSubobject((ker ψ).arrow ≫ p ≫ pageπ) ≤ imageSubobject(ofLE ≫ pageπ)

  -- === Setup: kerZ1 (deeper cycles), β : kerZ1 → kerZ, p1, h_factor ===
  set f_n1 := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) with hf_n1_def
  set kerZ1 := kernelSubobject f_n1 with hkerZ1_def
  have hkerZ1_le : kerZ1 ≤ kerZ := by
    apply le_kernelSubobject
    have hfil : FC.filtration.F (s + ↑(n + 1)) (k - 1) ≤ FC.filtration.F (s + ↑n) (k - 1) :=
      FC.filtration.le_of_le (by omega) (k - 1)
    have h1' : (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      simp only [Category.assoc]; exact kernelSubobject_arrow_comp f_n1
    set lift1 := Abelian.monoLift (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow
      (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) h1'
    calc kerZ1.arrow ≫ f_n
        = (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          simp only [f_n, Category.assoc]
      _ = (lift1 ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          rw [Abelian.monoLift_comp]
      _ = lift1 ≫ (Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          rw [show (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow =
            Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow
            from (Subobject.ofLE_arrow hfil).symm]; simp only [Category.assoc]
      _ = 0 := by simp only [Category.assoc, cokernel.condition, comp_zero]
  set β := Subobject.ofLE kerZ1 kerZ hkerZ1_le with hβ_def
  set p1 := factorThruImageSubobject (kerZ1.arrow ≫ πV) with hp1_def
  haveI hp1_epi : Epi p1 := inferInstance
  have h_Zn_eq : FC.cycleSubobject s k ↑n = imageSubobject (kerZ.arrow ≫ πV) := by
    subst kerZ
    subst f_n
    subst πV
    rfl
  have h_Zn1_eq : FC.cycleSubobject s k ↑(n + 1) =
      imageSubobject (kerZ1.arrow ≫ πV) := by
    subst kerZ1
    subst f_n1
    subst πV
    rfl
  have h_factor : p1 ≫ Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
      (FC.cycleSubobject s k ↑n)
      (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) = β ≫ p := by
    change p1 ≫ Subobject.ofLE
      (imageSubobject (kerZ1.arrow ≫ πV))
      (imageSubobject (kerZ.arrow ≫ πV)) _ = β ≫ p
    apply (inferInstance : Mono (imageSubobject (kerZ.arrow ≫ πV)).arrow).right_cancellation
    simp only [Category.assoc, p1, p, β]
    rw [Subobject.ofLE_arrow]
    erw [imageSubobject_arrow_comp, imageSubobject_arrow_comp]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  -- Key abbreviation: h_p_Z
  have h_p_Z : p ≫ (FC.cycleSubobject s k ↑n).arrow = kerZ.arrow ≫ πV := by
    change p ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow = kerZ.arrow ≫ πV
    exact imageSubobject_arrow_comp (kerZ.arrow ≫ πV)
  -- === Step 1: Factor (ker ψ).arrow ≫ to_Z_n_t through ker(pageπ_t) ===
  have h_to_Z_kills : ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ pageπ_t = 0 := by
    simp only [Category.assoc]; rw [← hψ_def]; exact kernelSubobject_arrow_comp ψ
  -- B_n_t and (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) at the target
  set B_n_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑n with hB_n_t_def
  have hB_le_Z := FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n
  -- to_Z_n_t ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow = lift_n ≫ πV'
  have h_to_Z_comp : to_Z_n_t ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow = lift_n ≫ πV' := by
    change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
      (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
    simp only [Category.assoc, imageSubobject_arrow_comp]
    rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
      (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm, h_ltk_spec]
  -- (ker ψ).arrow ≫ lift_n ≫ πV' = ((ker ψ).arrow ≫ to_Z_n_t) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow
  have h_lift_πV'_eq : (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
      ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow := by
    rw [Category.assoc, h_to_Z_comp]
  -- Factor (ker ψ).arrow ≫ lift_n ≫ πV' through B_n_t using exactness + ψ = 0
  have h_bnd_factors : B_n_t.Factors ((kernelSubobject ψ).arrow ≫ lift_n ≫ πV') := by
    rw [h_lift_πV'_eq]
    -- Factor (ker ψ).arrow ≫ to_Z_n_t through ofLE(B_n_t, (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)) using h_to_Z_kills
    set γ₁ := factorThruKernelSubobject pageπ_t
      ((kernelSubobject ψ).arrow ≫ to_Z_n_t) h_to_Z_kills
    -- γ₁ ≫ (ker pageπ_t).arrow = (ker ψ).arrow ≫ to_Z_n_t
    have hγ₁_spec : γ₁ ≫ (kernelSubobject pageπ_t).arrow =
        (kernelSubobject ψ).arrow ≫ to_Z_n_t :=
      factorThruKernelSubobject_comp_arrow _ _ _
    -- By exact_cokernel, imageSubobject(ofLE(B,Z)) = kernelSubobject(pageπ_t)
    have h_exact : (ShortComplex.mk (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) pageπ_t
        (by simp only [hpageπ_t_def]; exact cokernel.condition _)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _
        (by simp only [hpageπ_t_def]; exact cokernelIsCokernel _)
    rw [ShortComplex.exact_iff_image_eq_kernel] at h_exact
    change imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) = kernelSubobject pageπ_t at h_exact
    -- h_exact : imageSubobject(ofLE(B,Z)) = kernelSubobject(pageπ_t)
    -- Since ofLE(B,Z) is mono, factorThruImage(ofLE(B,Z)) is an iso
    haveI : Mono (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) := inferInstance
    haveI h_fti_epi : Epi (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)) :=
      inferInstance
    haveI h_fti_mono : Mono (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)) :=
      mono_of_mono_fac (imageSubobject_arrow_comp _)
    haveI : IsIso (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)) :=
      isIso_of_mono_of_epi _
    -- (ker pageπ_t).arrow ≫ Z.arrow factors through B.arrow
    have h_ker_Z_fac : B_n_t.Factors ((kernelSubobject pageπ_t).arrow ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow) := by
      rw [show (kernelSubobject pageπ_t).arrow =
        eqToHom (congr_arg Subobject.underlying.obj h_exact.symm) ≫
        (imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)).arrow from
        (Subobject.arrow_congr _ _ h_exact.symm).symm, Category.assoc]
      apply Subobject.factors_of_factors_right
      -- B_n_t.Factors(image(ofLE(B,Z)).arrow ≫ Z.arrow)
      have h_arrow_eq : (imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)).arrow ≫
          (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow =
        inv (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)) ≫
          B_n_t.arrow := by
        rw [← cancel_epi (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z))]
        -- Goal: factorThruImage ≫ image.arrow ≫ Z.arrow = B_n_t.arrow
        rw [show factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) ≫
          (imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)).arrow ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow =
          (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) ≫
          (imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)).arrow) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow
          from (Category.assoc _ _ _).symm,
          imageSubobject_arrow_comp, Subobject.ofLE_arrow,
          IsIso.hom_inv_id_assoc]
      rw [h_arrow_eq]
      exact Subobject.factors_comp_arrow _
    -- Combine: ((ker ψ).arrow ≫ to_Z_n_t) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow = γ₁ ≫ (ker pageπ_t).arrow ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow
    -- which factors through B_n_t
    rw [show ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow =
      (γ₁ ≫ (kernelSubobject pageπ_t).arrow) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow from by
        exact congrArg (fun t => t ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow)
          hγ₁_spec.symm,
      Category.assoc]
    exact Subobject.factors_of_factors_right _ h_ker_Z_fac
  -- α : the factoring morphism (ker ψ) → B_n_t
  set α := B_n_t.factorThru _ h_bnd_factors with hα_def
  have hα_spec : α ≫ B_n_t.arrow = (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' :=
    Subobject.factorThru_arrow _ _ _
  -- imgD_bnd, I_bnd, oI_bnd: the d-image subobject and its intersection with the filtration
  set imgD_bnd := imageSubobject ((FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
    FC.dToK (k - 1)) with himgD_bnd_def
  set I_bnd := imgD_bnd ⊓ FC.filtration.F (s + ↑n) (k - 1) with hI_bnd_def
  set oI_bnd := Subobject.ofLE I_bnd (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right
    with hoI_bnd_def
  -- factorB : I_bnd → B_n_t is epi
  set factorB := factorThruImageSubobject (oI_bnd ≫ πV') with hfactorB_def
  haveI hfactorB_epi : Epi factorB := inferInstance
  have hfactorB_spec : factorB ≫ B_n_t.arrow = oI_bnd ≫ πV' := by
    change factorThruImageSubobject (oI_bnd ≫ πV') ≫
      (imageSubobject (oI_bnd ≫ πV')).arrow = oI_bnd ≫ πV'
    exact imageSubobject_arrow_comp (oI_bnd ≫ πV')
  -- PB1: pullback of factorB (epi) against α
  set pb1_fst := Limits.pullback.fst factorB α
  set pb1_snd := Limits.pullback.snd factorB α
  have hpb1_cond : pb1_fst ≫ factorB = pb1_snd ≫ α := Limits.pullback.condition
  haveI : Epi pb1_snd := Abelian.epi_pullback_of_epi_f factorB α
  -- Key equation from PB1
  have h_pb1_eq_πV' : pb1_snd ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
      pb1_fst ≫ oI_bnd ≫ πV' := by
    calc pb1_snd ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV'
        = pb1_snd ≫ (α ≫ B_n_t.arrow) := by rw [hα_spec]
      _ = (pb1_snd ≫ α) ≫ B_n_t.arrow := (Category.assoc _ _ _).symm
      _ = (pb1_fst ≫ factorB) ≫ B_n_t.arrow := by
        exact congrArg (fun t => t ≫ B_n_t.arrow) hpb1_cond.symm
      _ = pb1_fst ≫ (factorB ≫ B_n_t.arrow) := Category.assoc _ _ _
      _ = pb1_fst ≫ oI_bnd ≫ πV' := by simp only [hfactorB_spec]
  -- PB2: pullback of factorD (epi) against pb1_fst ≫ oI_to_imgD
  set imgD_src := (FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)
    with himgD_src_def
  set factorD := factorThruImageSubobject imgD_src with hfactorD_def
  haveI hfactorD_epi : Epi factorD := inferInstance
  have hfactorD_spec : factorD ≫ imgD_bnd.arrow = imgD_src :=
    imageSubobject_arrow_comp imgD_src
  set oI_to_imgD := Subobject.ofLE I_bnd imgD_bnd inf_le_left with hoI_to_imgD_def
  set pb2_fst := Limits.pullback.fst factorD (pb1_fst ≫ oI_to_imgD)
  set pb2_snd := Limits.pullback.snd factorD (pb1_fst ≫ oI_to_imgD)
  have hpb2_cond : pb2_fst ≫ factorD = pb2_snd ≫ (pb1_fst ≫ oI_to_imgD) :=
    Limits.pullback.condition
  haveI : Epi pb2_snd := Abelian.epi_pullback_of_epi_f factorD _
  -- Composite epi
  set e := pb2_snd ≫ pb1_snd with he_def
  haveI : Epi e := epi_comp _ _
  -- Correction term σ
  set eqH := eqToHom (show Subobject.underlying.obj (FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)) =
    Subobject.underlying.obj (FC.filtration.F (s + 1) k) from by
    rw [show (s : ℤ) + ↑n - ↑n + 1 = s + 1 from by omega,
        show (k : ℤ) - 1 + 1 = k from by omega]) with heqH_def
  set σ := pb2_fst ≫ eqH ≫ ι_s with hσ_def
  -- σ ≫ πV = 0
  have hσ_πV : σ ≫ πV = 0 := by
    simp only [hσ_def, Category.assoc, show ι_s ≫ πV = 0 from cokernel.condition ι_s,
      comp_zero]
  -- w factors through kerZ1
  set w := e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow - σ with hw_def
  have hw_kills : w ≫ f_n1 = 0 := by
    rw [hw_def, Preadditive.sub_comp, sub_eq_zero]
    -- Goal: (e ≫ (ker ψ).arrow ≫ kerZ.arrow) ≫ f_n1 = σ ≫ f_n1
    -- Strategy: show both sides equal pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫ cokernel.π(...)
    --
    -- Key auxiliary facts:
    have h_sn1_eq : (s : ℤ) + ↑n + 1 = s + ↑(n + 1) := by push_cast; omega
    -- (1) e ≫ (ker ψ).arrow ≫ lift_n ≫ πV' = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ πV'
    have h_e_lift_πV' : e ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
        pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ πV' := by
      simp only [he_def, Category.assoc, h_pb1_eq_πV']
    -- (2) The difference (e ≫ ... ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd) ≫ πV' = 0
    have h_diff_kills : (e ≫ (kernelSubobject ψ).arrow ≫ lift_n -
        pb2_snd ≫ pb1_fst ≫ oI_bnd) ≫ πV' = 0 := by
      rw [Preadditive.sub_comp]; simp only [Category.assoc]
      rw [h_e_lift_πV', sub_self]
    -- (3) monoLift decomposes the difference
    set γ_diff := Abelian.monoLift ι_t
        (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd)
        (show _ ≫ cokernel.π ι_t = 0 from h_diff_kills) with hγ_diff_def
    have hγ_spec : γ_diff ≫ ι_t =
        e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd :=
      Abelian.monoLift_comp ι_t
        (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd)
        (show _ ≫ cokernel.π ι_t = 0 from h_diff_kills)
    have h_decomp : e ≫ (kernelSubobject ψ).arrow ≫ lift_n =
        pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t := by
      -- hγ_spec: γ_diff ≫ ι_t = (e ≫ ...) - (pb2_snd ≫ ...)
      -- eq_add_of_sub_eq: a - b = c → a = b + c ... wait, sub_eq_iff_eq_add flipped
      -- From c = a - b we get a = c + b (sub_eq_iff_eq_add)
      -- Then a = b + c by add_comm
      -- Actually: hγ_spec.symm : (e ≫ ...) - (pb2_snd ≫ ...) = γ_diff ≫ ι_t
      -- sub_eq_iff_eq_add.mp hγ_spec.symm : e ≫ ... = γ_diff ≫ ι_t + pb2_snd ≫ ...
      -- But sub_eq_iff_eq_add.mp causes motive error.
      -- Direct arithmetic approach:
      have key : e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd =
          γ_diff ≫ ι_t := hγ_spec.symm
      -- a - b = c → a = b + c
      calc e ≫ (kernelSubobject ψ).arrow ≫ lift_n
          = (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd) +
            pb2_snd ≫ pb1_fst ≫ oI_bnd := (sub_add_cancel _ _).symm
        _ = γ_diff ≫ ι_t + pb2_snd ≫ pb1_fst ≫ oI_bnd := by rw [key]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t := add_comm _ _
    -- (4) ι_t ≫ F^{s+n}.arrow ≫ cokernel.π(F^{s+↑(n+1)}.arrow) = 0
    have h_ι_t_kills : ι_t ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      have h1 : ι_t ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
          (FC.filtration.F (s + ↑n + 1) (k - 1)).arrow :=
        Subobject.ofLE_arrow (FC.filtration.decreasing (s + ↑n) (k - 1))
      have h2 : (FC.filtration.F (s + ↑n + 1) (k - 1)).arrow =
          eqToHom (congr_arg (fun i => Subobject.underlying.obj (FC.filtration.F i (k - 1)))
            h_sn1_eq) ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow := by
        simp [h_sn1_eq]
      calc ι_t ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow)
          = (ι_t ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) := by
            rw [Category.assoc]
        _ = (eqToHom _ ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) := by
            rw [h1, h2]
        _ = eqToHom _ ≫ ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow)) := by
            rw [Category.assoc]
        _ = eqToHom _ ≫ 0 := by
            rw [cokernel.condition]
        _ = 0 := by rw [comp_zero]
    -- (5) oI_bnd ≫ F^{s+n}.arrow = I_bnd.arrow
    have h_oI_arrow : oI_bnd ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow = I_bnd.arrow :=
      Subobject.ofLE_arrow inf_le_right
    -- (6) σ ≫ F^s.arrow = pb2_fst ≫ eqH ≫ F^{s+1}.arrow
    have h_σ_arrow : σ ≫ (FC.filtration.F s k).arrow =
        pb2_fst ≫ eqH ≫ (FC.filtration.F (s + 1) k).arrow := by
      simp only [hσ_def, Category.assoc]
      congr 2; exact Subobject.ofLE_arrow (FC.filtration.decreasing s k)
    -- (7) eqH ≫ F^{s+1}.arrow ≫ d(k) = imgD_src
    have h_eqH_d : eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) = imgD_src := by
      conv_lhs => rw [← eqToHom_arrow_dToK_local FC (s + 1) k]
      rw [heqH_def]; simp only [← Category.assoc]; rw [eqToHom_trans]
      -- Goal: (eqToHom _ ≫ (FC.filtration.F (s+1)((k-1)+1)).arrow) ≫ FC.dToK (k-1) = imgD_src
      -- imgD_src = (FC.filtration.F (s+↑n-↑n+1) ((k-1)+1)).arrow ≫ FC.dToK (k-1)
      -- Since s+↑n-↑n+1 = s+1, both sides are equal
      rw [himgD_src_def]
      -- Goal: (eqToHom _ ≫ (FC.filtration.F (s+1)((k-1)+1)).arrow) ≫ FC.dToK (k-1) =
      --       (FC.filtration.F (s+↑n-↑n+1) ((k-1)+1)).arrow ≫ FC.dToK (k-1)
      congr 1
      -- Goal: eqToHom _ ≫ (FC.filtration.F (s+1)((k-1)+1)).arrow = (FC.filtration.F (s+↑n-↑n+1) ((k-1)+1)).arrow
      exact Subobject.arrow_congr _ _ (by congr 1; omega)
    -- (8) pb2_fst ≫ imgD_src = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow
    have h_pb2_imgD : pb2_fst ≫ imgD_src = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow := by
      calc pb2_fst ≫ imgD_src
          = pb2_fst ≫ (factorD ≫ imgD_bnd.arrow) := by
            rw [imageSubobject_arrow_comp imgD_src]
        _ = (pb2_fst ≫ factorD) ≫ imgD_bnd.arrow := by rw [Category.assoc]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_to_imgD) ≫ imgD_bnd.arrow := by rw [hpb2_cond]
        _ = pb2_snd ≫ pb1_fst ≫ (oI_to_imgD ≫ imgD_bnd.arrow) := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow := by
            congr 1; congr 1; exact Subobject.ofLE_arrow inf_le_left
    -- === LHS: (e ≫ (ker ψ).arrow ≫ kerZ.arrow) ≫ f_n1 ===
    have h_lhs : (e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow) ≫ f_n1 =
        pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) := by
      -- Expand and right-associate
      rw [hf_n1_def]; simp only [Category.assoc]
      -- Step 1: Replace kerZ.arrow ≫ F^s.arrow ≫ d k with lift_n ≫ F^{s+n}.arrow
      conv_lhs =>
        rw [show (kernelSubobject ψ).arrow ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) =
            (kernelSubobject ψ).arrow ≫ (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [← h_lift_spec]
      simp only [Category.assoc]
      -- Goal: e ≫ (ker ψ).arrow ≫ lift_n ≫ F^{s+n}.arrow ≫ cokernel.π = pb2_snd ≫ ...
      -- Step 2-5: Use calc with explicit left-association
      set F_sn := (FC.filtration.F (s + ↑n) (k - 1)).arrow with hF_sn_def
      set cok := cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) with hcok_def
      calc e ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ F_sn ≫ cok
          = (e ≫ (kernelSubobject ψ).arrow ≫ lift_n) ≫ F_sn ≫ cok := by
            simp only [Category.assoc]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t) ≫ F_sn ≫ cok := by
            rw [h_decomp]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_bnd) ≫ F_sn ≫ cok +
            (γ_diff ≫ ι_t) ≫ F_sn ≫ cok := by
            rw [Preadditive.add_comp]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok +
            γ_diff ≫ ι_t ≫ F_sn ≫ cok := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok + γ_diff ≫ 0 := by
            rw [h_ι_t_kills]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok + 0 := by
            rw [comp_zero]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok := by
            rw [add_zero]
        _ = pb2_snd ≫ pb1_fst ≫ (oI_bnd ≫ F_sn) ≫ cok := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫ cok := by
            rw [h_oI_arrow]
    -- === RHS: σ ≫ f_n1 ===
    have h_rhs : σ ≫ f_n1 =
        pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) := by
      rw [hf_n1_def]
      -- σ ≫ F^s.arrow ≫ d(k) ≫ cokernel.π = pb2_fst ≫ eqH ≫ F^{s+1}.arrow ≫ d(k) ≫ cokernel.π
      conv_lhs =>
        rw [show σ ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) =
            (σ ≫ (FC.filtration.F s k).arrow) ≫ FC.complex.d k (k - 1) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [h_σ_arrow]
      simp only [Category.assoc]
      -- pb2_fst ≫ eqH ≫ F^{s+1}.arrow ≫ d(k) ≫ cokernel.π
      conv_lhs =>
        rw [show pb2_fst ≫ eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) =
            (pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1))) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [show pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1)) =
            (pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1))) from rfl]
      conv_lhs =>
        rw [show (pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1))) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) =
            pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
      rw [h_eqH_d]
      simp only [← Category.assoc]; rw [h_pb2_imgD]; simp only [Category.assoc]
    rw [h_lhs, h_rhs]
  -- w_fac : PB2 → kerZ1
  set w_fac := factorThruKernelSubobject f_n1 w hw_kills with hw_fac_def
  have hw_fac_spec : w_fac ≫ kerZ1.arrow = w :=
    factorThruKernelSubobject_comp_arrow _ _ _
  -- Key equation: w_fac ≫ β ≫ p = e ≫ (ker ψ).arrow ≫ p (by mono cancellation)
  have h_key_eq : w_fac ≫ β ≫ p = e ≫ (kernelSubobject ψ).arrow ≫ p := by
    apply (inferInstance : Mono (FC.cycleSubobject s k ↑n).arrow).right_cancellation
    calc
      (w_fac ≫ β ≫ p) ≫ (FC.cycleSubobject s k ↑n).arrow =
          w_fac ≫ β ≫ (p ≫ (FC.cycleSubobject s k ↑n).arrow) := by
            simp only [Category.assoc]
      _ = w_fac ≫ β ≫ (kerZ.arrow ≫ πV) := by rw [h_p_Z]
      _ = (w_fac ≫ (β ≫ kerZ.arrow)) ≫ πV := by
            simp only [Category.assoc]
      _ = (w_fac ≫ kerZ1.arrow) ≫ πV := by
            rw [Subobject.ofLE_arrow hkerZ1_le]
      _ = w ≫ πV := by rw [hw_fac_spec]
      _ = (e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow - σ) ≫ πV := by
            rw [hw_def]
      _ = (e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow) ≫ πV := by
            rw [Preadditive.sub_comp, hσ_πV, sub_zero]
      _ = e ≫ (kernelSubobject ψ).arrow ≫ (kerZ.arrow ≫ πV) := by
            simp only [Category.assoc]
      _ = e ≫ (kernelSubobject ψ).arrow ≫ (p ≫
          (FC.cycleSubobject s k ↑n).arrow) := by rw [h_p_Z]
      _ = (e ≫ (kernelSubobject ψ).arrow ≫ p) ≫
          (FC.cycleSubobject s k ↑n).arrow := by
            simp only [Category.assoc]
  -- Conclusion: use epi_comp', h_key_eq, h_factor to show
  --   imageSubobject((ker ψ).arrow ≫ p ≫ pageπ) ≤ imageSubobject(ofLE ≫ pageπ)
  -- Step 1: imageSubobject_epi_comp'_local removes e
  rw [(imageSubobject_epi_comp'_local e
    ((kernelSubobject ψ).arrow ≫ p ≫ FC.pageπ s k ↑n)).symm]
  -- Goal: imageSubobject(e ≫ (ker ψ).arrow ≫ p ≫ pageπ) ≤ imageSubobject(ofLE ≫ pageπ)
  -- Step 2: rewrite e ≫ ... = (w_fac ≫ p1) ≫ (ofLE ≫ pageπ)
  have h_rewrite : e ≫ (kernelSubobject ψ).arrow ≫ p ≫ FC.pageπ s k ↑n =
      (w_fac ≫ p1) ≫ (Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
        (FC.cycleSubobject s k ↑n)
        (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
        FC.pageπ s k ↑n) := by
    simp only [FilteredComplex.cycleSubobject]
    have h_img_le : imageSubobject (kerZ1.arrow ≫ πV) ≤
        imageSubobject (kerZ.arrow ≫ πV) := by
      rw [show kerZ1.arrow ≫ πV = (β ≫ kerZ.arrow) ≫ πV by
        rw [Subobject.ofLE_arrow hkerZ1_le]]
      simpa only [Category.assoc] using imageSubobject_comp_le β (kerZ.arrow ≫ πV)
    change e ≫ (kernelSubobject ψ).arrow ≫ (p ≫ FC.pageπ s k ↑n) =
      (w_fac ≫ p1) ≫
        (Subobject.ofLE (imageSubobject (kerZ1.arrow ≫ πV))
          (imageSubobject (kerZ.arrow ≫ πV)) h_img_le ≫ FC.pageπ s k ↑n)
    have h_factor_image : p1 ≫ Subobject.ofLE
        (imageSubobject (kerZ1.arrow ≫ πV))
        (imageSubobject (kerZ.arrow ≫ πV)) h_img_le = β ≫ p := by
      change p1 ≫ Subobject.ofLE
        (imageSubobject (kerZ1.arrow ≫ πV))
        (imageSubobject (kerZ.arrow ≫ πV)) h_img_le = β ≫ p at h_factor
      exact h_factor
    have h_prefix : e ≫ (kernelSubobject ψ).arrow ≫ p =
        w_fac ≫ p1 ≫ Subobject.ofLE
          (imageSubobject (kerZ1.arrow ≫ πV))
          (imageSubobject (kerZ.arrow ≫ πV)) h_img_le := by
      rw [← h_key_eq]
      congr 1
      exact h_factor_image.symm
    rw [← Category.assoc e (kernelSubobject ψ).arrow
      (p ≫ FC.pageπ s k ↑n)]
    rw [← Category.assoc (e ≫ (kernelSubobject ψ).arrow) p
      (FC.pageπ s k ↑n)]
    have h_prefix_left :
        ((e ≫ (kernelSubobject ψ).arrow) ≫ p) =
          w_fac ≫ p1 ≫ Subobject.ofLE
            (imageSubobject (kerZ1.arrow ≫ πV))
            (imageSubobject (kerZ.arrow ≫ πV)) h_img_le := by
      rw [show ((e ≫ (kernelSubobject ψ).arrow) ≫ p) =
        e ≫ (kernelSubobject ψ).arrow ≫ p from by simp only [Category.assoc],
        h_prefix]
    rw [h_prefix_left]
    simp only [Category.assoc]
  rw [h_rewrite]
  exact imageSubobject_comp_le _ _




set_option maxHeartbeats 6400000 in
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
      simp only [Category.assoc, Subobject.ofLE_arrow, hfactorγ_spec]
      rfl
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
    rw [show (w ≫ lift_to_kerZ') ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n =
      w ≫ (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ FC.pageπ (s + ↑n) (k - 1) ↑n) from by
      simp only [Category.assoc]]
    exact imageSubobject_comp_le _ _
end KIP126.Core.SpectralSequence.FilteredComplex
