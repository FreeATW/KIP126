import KIP126.Def.SpectralSequence.FilteredDifferential.Data
import KIP126.Def.SpectralSequence.FilteredPage.Proofs

/-! # Square-zero law for the filtered-page differential -/

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


end KIP126.Core.SpectralSequence.FilteredComplex
