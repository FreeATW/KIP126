/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Unbounded extension spectral sequence via truncation and stabilization.
Reference: informal/unbounded_extension.md
-/

import KIPBase.SpectralSequence.BoundedExtension
import KIPBase.SpectralSequence.Completion

universe u v w

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
variable {ω' : Type w}
variable {E₁ E₂ : SpectralSequence C ω}
variable {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
variable {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}

/-! ### Section 1: Truncated extension spectral sequence -/

noncomputable def truncatedUnderlyingComplex
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') :
    FilteredComplex C :=
  underlyingComplex
    (fun k' => cm.truncatedAMap s₀ k')
    (fun s k' => cm.truncatedFiltrationCompat s₀ s k')
    t

noncomputable def truncatedUnderlyingComplex_isBounded
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') :
    (truncatedUnderlyingComplex cm s₀ t).IsBounded :=
  underlyingComplexBounded
    (fun k' => cm.truncatedAMap s₀ k')
    (fun s k' => cm.truncatedFiltrationCompat s₀ s k')
    t
    (F₁.truncatedFiltration_isBounded hbb₁ s₀)
    (F₂.truncatedFiltration_isBounded hbb₂ s₀)

noncomputable def truncatedESS
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  (truncatedUnderlyingComplex cm s₀ t).toSpectralSequence
    (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t)

/-! ### Section 2: Inverse system structure -/

/-- The truncation transition preserves the truncated filtration of F₁. -/
private theorem truncationTransition_fil_compat₁
    {s₀ s₁ : ℤ} (hle : s₀ ≤ s₁) (s' : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj ((F₁.truncatedFiltration s₁).F s' k') ⟶
           Subobject.underlying.obj ((F₁.truncatedFiltration s₀).F s' k')),
      φ ≫ ((F₁.truncatedFiltration s₀).F s' k').arrow =
        ((F₁.truncatedFiltration s₁).F s' k').arrow ≫ F₁.truncationTransition hle k' := by
  have sq_comm : 𝟙 _ ≫ ((F₁.F s' k').arrow ≫ F₁.truncationProj s₀ k') =
      ((F₁.F s' k').arrow ≫ F₁.truncationProj s₁ k') ≫ F₁.truncationTransition hle k' := by
    simp only [Category.id_comp, Category.assoc, F₁.truncationProj_transition hle k']
  exact ⟨imageSubobjectMap (Arrow.homMk (𝟙 _) (F₁.truncationTransition hle k') sq_comm),
         imageSubobjectMap_arrow _⟩

/-- The truncation transition preserves the truncated filtration of F₂. -/
private theorem truncationTransition_fil_compat₂
    {s₀ s₁ : ℤ} (hle : s₀ ≤ s₁) (s' : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj ((F₂.truncatedFiltration s₁).F s' k') ⟶
           Subobject.underlying.obj ((F₂.truncatedFiltration s₀).F s' k')),
      φ ≫ ((F₂.truncatedFiltration s₀).F s' k').arrow =
        ((F₂.truncatedFiltration s₁).F s' k').arrow ≫ F₂.truncationTransition hle k' := by
  have sq_comm : 𝟙 _ ≫ ((F₂.F s' k').arrow ≫ F₂.truncationProj s₀ k') =
      ((F₂.F s' k').arrow ≫ F₂.truncationProj s₁ k') ≫ F₂.truncationTransition hle k' := by
    simp only [Category.id_comp, Category.assoc, F₂.truncationProj_transition hle k']
  exact ⟨imageSubobjectMap (Arrow.homMk (𝟙 _) (F₂.truncationTransition hle k') sq_comm),
         imageSubobjectMap_arrow _⟩

/-- Naturality: truncatedAMap commutes with truncation transitions.
    F₁.truncationTransition ≫ cm.truncatedAMap s₀ = cm.truncatedAMap s₁ ≫ F₂.truncationTransition -/
private theorem truncatedAMap_naturality
    (cm : ConvergenceMorphism conv₁ conv₂)
    {s₀ s₁ : ℤ} (hle : s₀ ≤ s₁) (k' : ω') :
    F₁.truncationTransition hle k' ≫ cm.truncatedAMap s₀ k' =
      cm.truncatedAMap s₁ k' ≫ F₂.truncationTransition hle k' := by
  haveI : Epi (F₁.truncationProj s₁ k') := by
    unfold Filtration.truncationProj; infer_instance
  suffices key : F₁.truncationProj s₁ k' ≫ F₁.truncationTransition hle k' ≫
      cm.truncatedAMap s₀ k' =
      F₁.truncationProj s₁ k' ≫ cm.truncatedAMap s₁ k' ≫
      F₂.truncationTransition hle k' from (cancel_epi (F₁.truncationProj s₁ k')).mp key
  have lhs_eq : F₁.truncationProj s₁ k' ≫ F₁.truncationTransition hle k' ≫
      cm.truncatedAMap s₀ k' = cm.aMap k' ≫ F₂.truncationProj s₀ k' := by
    rw [← Category.assoc, F₁.truncationProj_transition hle k']
    simp [Filtration.truncationProj, ConvergenceMorphism.truncatedAMap, cokernel.π_desc]
  have rhs_eq : F₁.truncationProj s₁ k' ≫ cm.truncatedAMap s₁ k' ≫
      F₂.truncationTransition hle k' = cm.aMap k' ≫ F₂.truncationProj s₀ k' := by
    have h_proj : F₁.truncationProj s₁ k' ≫ cm.truncatedAMap s₁ k' =
        cm.aMap k' ≫ F₂.truncationProj s₁ k' := by
      simp [Filtration.truncationProj, ConvergenceMorphism.truncatedAMap, cokernel.π_desc]
    rw [← Category.assoc, h_proj, Category.assoc, F₂.truncationProj_transition hle k']
  rw [lhs_eq, rhs_eq]

/-- The assocGraded of the truncated underlying complex at k=1 equals
    the associatedGraded of the F₁ truncated filtration. -/
private theorem truncatedUC_assocGraded_one
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ) :
    (truncatedUnderlyingComplex cm s₀ t).assocGraded s 1 =
      (F₁.truncatedFiltration s₀).associatedGraded s t := by
  simp only [truncatedUnderlyingComplex, underlyingComplex,
    FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
  congr 1

/-- The assocGraded of the truncated underlying complex at k=0 equals
    the associatedGraded of the F₂ truncated filtration. -/
private theorem truncatedUC_assocGraded_zero
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ) :
    (truncatedUnderlyingComplex cm s₀ t).assocGraded s 0 =
      (F₂.truncatedFiltration s₀).associatedGraded s t := by
  simp only [truncatedUnderlyingComplex, underlyingComplex,
    FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
  congr 1

private lemma imageSubobject_eq_top_of_zero_comp_epi {X Y Z : C}
    (g : X ⟶ Y) [Epi g] :
    imageSubobject ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g) = ⊤ := by
  haveI : IsIso (kernelSubobject (0 : X ⟶ Z)).arrow := isIso_kernelSubobject_zero_arrow
  have : Epi ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g) := epi_comp _ _
  have : Epi (imageSubobject ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g)).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp _)
  haveI : IsIso (imageSubobject ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g)).arrow :=
    isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

private lemma imageSubobject_ofLE_bot_comp_eq_bot {X : C} (a : Subobject X)
    {Y : C} (g : Subobject.underlying.obj a ⟶ Y) :
    imageSubobject (Subobject.ofLE ⊥ a bot_le ≫ g) = ⊥ := by
  have h : Subobject.ofLE (⊥ : Subobject X) a bot_le = 0 := by
    have h1 := Subobject.ofLE_arrow (X := (⊥ : Subobject X)) (Y := a) bot_le
    rw [Subobject.bot_arrow] at h1
    exact (cancel_mono a.arrow).mp (by simp [h1])
  simp [h, zero_comp, imageSubobject_zero]

private theorem truncatedUC_cycleSubobject_zero_eq_top
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ)
    (r : WithTop ℕ) :
    (truncatedUnderlyingComplex cm s₀ t).cycleSubobject s 0 r = ⊤ := by
  have h_d_zero : (truncatedUnderlyingComplex cm s₀ t).d 0 = 0 := by
    simp [truncatedUnderlyingComplex, underlyingComplex, twoTermDiff]
  delta FilteredComplex.cycleSubobject
  cases r with
  | top =>
    dsimp only []
    convert imageSubobject_eq_top_of_zero_comp_epi
      (Z := (truncatedUnderlyingComplex cm s₀ t).A (0 - 1))
      (cokernel.π (((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 0).ofLE
        ((truncatedUnderlyingComplex cm s₀ t).fil s 0) (FilteredComplex.fil_anti _ s 0)))
      <;> first | rfl | rw [h_d_zero, comp_zero]
  | coe n =>
    dsimp only []
    convert imageSubobject_eq_top_of_zero_comp_epi
      (Z := cokernel ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (0 - 1)).arrow)
      (cokernel.π (((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 0).ofLE
        ((truncatedUnderlyingComplex cm s₀ t).fil s 0) (FilteredComplex.fil_anti _ s 0)))
      <;> first | rfl | simp [h_d_zero, comp_zero, zero_comp]

private theorem truncatedUC_boundarySubobject_one_eq_bot
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ)
    (r : WithTop ℕ) :
    (truncatedUnderlyingComplex cm s₀ t).boundarySubobject s 1 r = ⊥ := by
  have h_dToK_zero : (truncatedUnderlyingComplex cm s₀ t).dToK 1 = 0 := by
    simp [FilteredComplex.dToK, truncatedUnderlyingComplex, underlyingComplex, twoTermDiff]
  delta FilteredComplex.boundarySubobject
  cases r with
  | top =>
    dsimp only []
    have h_I : imageSubobject ((truncatedUnderlyingComplex cm s₀ t).dToK 1) ⊓
        (truncatedUnderlyingComplex cm s₀ t).fil s 1 = ⊥ := by
      rw [h_dToK_zero, imageSubobject_zero, bot_inf_eq]
    convert imageSubobject_ofLE_bot_comp_eq_bot
      ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
      (cokernel.π (((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 1).ofLE
        ((truncatedUnderlyingComplex cm s₀ t).fil s 1) (FilteredComplex.fil_anti _ s 1)))
      <;> first | rfl | simpa using h_I
  | coe n =>
    dsimp only []
    have h_I : imageSubobject (((truncatedUnderlyingComplex cm s₀ t).fil (s - ↑n + 1) 2).arrow ≫
        (truncatedUnderlyingComplex cm s₀ t).dToK 1) ⊓
        (truncatedUnderlyingComplex cm s₀ t).fil s 1 = ⊥ := by
      rw [h_dToK_zero, comp_zero, imageSubobject_zero, bot_inf_eq]
    convert imageSubobject_ofLE_bot_comp_eq_bot
      ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
      (cokernel.π (((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 1).ofLE
        ((truncatedUnderlyingComplex cm s₀ t).fil s 1) (FilteredComplex.fil_anti _ s 1)))
      <;> first | rfl | simpa using h_I

/-- Given a commutative square on kernels and a compatible cokernel-projection square,
    imageSubobjectMap provides a lift for the composition `kernelSubobject.arrow ≫ πV`. -/
private lemma imageSubobjectMap_of_kernel_cokernel_square
    {X₁ Y₁ X₂ Y₂ V₁ V₂ : C}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    {left : X₁ ⟶ X₂} {right : Y₁ ⟶ Y₂}
    (sq_ker : left ≫ f₂ = f₁ ≫ right)
    {πV₁ : X₁ ⟶ V₁} {πV₂ : X₂ ⟶ V₂}
    {φ : V₁ ⟶ V₂}
    (h_πV : left ≫ πV₂ = πV₁ ≫ φ) :
    ∃ (lift : Subobject.underlying.obj (imageSubobject ((kernelSubobject f₁).arrow ≫ πV₁)) ⟶
              Subobject.underlying.obj (imageSubobject ((kernelSubobject f₂).arrow ≫ πV₂))),
      lift ≫ (imageSubobject ((kernelSubobject f₂).arrow ≫ πV₂)).arrow =
        (imageSubobject ((kernelSubobject f₁).arrow ≫ πV₁)).arrow ≫ φ := by
  let sq := Arrow.homMk (f := Arrow.mk f₁) (g := Arrow.mk f₂) left right sq_ker
  let ker_lift := kernelSubobjectMap sq
  have hker := kernelSubobjectMap_arrow sq
  have h_sq_left : sq.left = left := rfl
  have img_sq_comm : ker_lift ≫ ((kernelSubobject f₂).arrow ≫ πV₂) =
      ((kernelSubobject f₁).arrow ≫ πV₁) ≫ φ := by
    rw [Category.assoc, ← h_πV, ← Category.assoc, hker, h_sq_left, Category.assoc]
  let sq_img := Arrow.homMk
    (f := Arrow.mk ((kernelSubobject f₁).arrow ≫ πV₁))
    (g := Arrow.mk ((kernelSubobject f₂).arrow ≫ πV₂))
    ker_lift φ img_sq_comm
  exact ⟨imageSubobjectMap sq_img, imageSubobjectMap_arrow sq_img⟩

private theorem truncatedUC_cycleSubobject_one_preserved
    (cm : ConvergenceMorphism conv₁ conv₂)
    (_hbb₁ : F₁.IsBoundedBelow) (_hbb₂ : F₂.IsBoundedBelow)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (t : ω') (s : ℤ) (r : WithTop ℕ) :
    ∃ (lift : Subobject.underlying.obj
          ((truncatedUnderlyingComplex cm s₁ t).cycleSubobject s 1 r) ⟶
        Subobject.underlying.obj
          ((truncatedUnderlyingComplex cm s₀ t).cycleSubobject s 1 r)),
      lift ≫ ((truncatedUnderlyingComplex cm s₀ t).cycleSubobject s 1 r).arrow =
        ((truncatedUnderlyingComplex cm s₁ t).cycleSubobject s 1 r).arrow ≫
          (eqToHom (truncatedUC_assocGraded_one cm s₁ t s) ≫
            Filtration.inducedAssocGradedMap
              (fun k' => F₁.truncationTransition h k')
              (fun s' k' => truncationTransition_fil_compat₁ h s' k')
              s t ≫
            eqToHom (truncatedUC_assocGraded_one cm s₀ t s).symm) := by
  set grφ := eqToHom (truncatedUC_assocGraded_one cm s₁ t s) ≫
            Filtration.inducedAssocGradedMap
              (fun k' => F₁.truncationTransition h k')
              (fun s' k' => truncationTransition_fil_compat₁ h s' k')
              s t ≫
            eqToHom (truncatedUC_assocGraded_one cm s₀ t s).symm with hgrφ_def
  set compat_s := (truncationTransition_fil_compat₁ (F₁ := F₁) h s t).choose
  have hcompat_s := (truncationTransition_fil_compat₁ (F₁ := F₁) h s t).choose_spec
  delta FilteredComplex.cycleSubobject
  dsimp only []
  cases r with
  | top =>
    have h_grφ_simp : grφ =
        Filtration.inducedAssocGradedMap
          (fun k' => F₁.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₁ h s' k')
          s t := by
      simp only [grφ, truncatedUnderlyingComplex, underlyingComplex,
        FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have h_πV_comm : compat_s ≫
        cokernel.π (Subobject.ofLE
          ((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 1)
          ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
          (FilteredComplex.fil_anti (truncatedUnderlyingComplex cm s₀ t) s 1)) =
        cokernel.π (Subobject.ofLE
          ((truncatedUnderlyingComplex cm s₁ t).fil (s + 1) 1)
          ((truncatedUnderlyingComplex cm s₁ t).fil s 1)
          (FilteredComplex.fil_anti (truncatedUnderlyingComplex cm s₁ t) s 1)) ≫ grφ := by
      rw [h_grφ_simp]
      change compat_s ≫
          cokernel.π (Subobject.ofLE ((F₁.truncatedFiltration s₀).F (s + 1) t)
            ((F₁.truncatedFiltration s₀).F s t)
            ((F₁.truncatedFiltration s₀).mono s t)) =
        cokernel.π (Subobject.ofLE ((F₁.truncatedFiltration s₁).F (s + 1) t)
            ((F₁.truncatedFiltration s₁).F s t)
            ((F₁.truncatedFiltration s₁).mono s t)) ≫
          Filtration.inducedAssocGradedMap
            (fun k' => F₁.truncationTransition h k')
            (fun s' k' => truncationTransition_fil_compat₁ h s' k')
            s t
      simp only [Filtration.inducedAssocGradedMap]
      rw [cokernel.π_desc]
    have h_ker_sq : compat_s ≫
        (((truncatedUnderlyingComplex cm s₀ t).fil s 1).arrow ≫
          (truncatedUnderlyingComplex cm s₀ t).d 1) =
        (((truncatedUnderlyingComplex cm s₁ t).fil s 1).arrow ≫
          (truncatedUnderlyingComplex cm s₁ t).d 1) ≫
        F₂.truncationTransition h t := by
      simp only [truncatedUnderlyingComplex, underlyingComplex, twoTermDiff, twoTermFil,
        ↓reduceDIte, eqToHom_refl, Category.id_comp, Category.comp_id]
      simp only [Category.assoc]
      show compat_s ≫ ((F₁.truncatedFiltration s₀).F s t).arrow ≫
          cm.truncatedAMap s₀ t =
        ((F₁.truncatedFiltration s₁).F s t).arrow ≫
          cm.truncatedAMap s₁ t ≫ F₂.truncationTransition h t
      rw [← truncatedAMap_naturality cm h t, ← Category.assoc,
        ← Category.assoc, hcompat_s, Category.assoc]
    exact imageSubobjectMap_of_kernel_cokernel_square h_ker_sq h_πV_comm
  | coe n =>
    -- grφ simplification: strip eqToHom wrappers
    have h_grφ_simp : grφ =
        Filtration.inducedAssocGradedMap
          (fun k' => F₁.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₁ h s' k')
          s t := by
      simp only [grφ, truncatedUnderlyingComplex, underlyingComplex,
        FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    -- πV commutativity in truncatedUnderlyingComplex terms (matching goal shape)
    have h_πV_comm : compat_s ≫
        cokernel.π (Subobject.ofLE
          ((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 1)
          ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
          (FilteredComplex.fil_anti (truncatedUnderlyingComplex cm s₀ t) s 1)) =
        cokernel.π (Subobject.ofLE
          ((truncatedUnderlyingComplex cm s₁ t).fil (s + 1) 1)
          ((truncatedUnderlyingComplex cm s₁ t).fil s 1)
          (FilteredComplex.fil_anti (truncatedUnderlyingComplex cm s₁ t) s 1)) ≫ grφ := by
      rw [h_grφ_simp]
      change compat_s ≫
          cokernel.π (Subobject.ofLE ((F₁.truncatedFiltration s₀).F (s + 1) t)
            ((F₁.truncatedFiltration s₀).F s t)
            ((F₁.truncatedFiltration s₀).mono s t)) =
        cokernel.π (Subobject.ofLE ((F₁.truncatedFiltration s₁).F (s + 1) t)
            ((F₁.truncatedFiltration s₁).F s t)
            ((F₁.truncatedFiltration s₁).mono s t)) ≫
          Filtration.inducedAssocGradedMap
            (fun k' => F₁.truncationTransition h k')
            (fun s' k' => truncationTransition_fil_compat₁ h s' k')
            s t
      simp only [Filtration.inducedAssocGradedMap]
      rw [cokernel.π_desc]
    -- Build the cokernel map on the right side, in truncatedUnderlyingComplex terms
    obtain ⟨φ_sn, hφ_sn⟩ := truncationTransition_fil_compat₂ (F₂ := F₂) h (s + ↑n) t
    have h_cok_cond : ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow ≫
        (F₂.truncationTransition h t ≫
          cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow) = 0 := by
      show ((F₂.truncatedFiltration s₁).F (s + ↑n) t).arrow ≫
        (F₂.truncationTransition h t ≫
          cokernel.π ((F₂.truncatedFiltration s₀).F (s + ↑n) t).arrow) = 0
      rw [← Category.assoc, ← hφ_sn, Category.assoc, cokernel.condition, comp_zero]
    let cok_right := cokernel.desc
      ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow
      (F₂.truncationTransition h t ≫
        cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow)
      h_cok_cond
    have h_cok_π : cokernel.π ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow ≫
        cok_right = F₂.truncationTransition h t ≫
        cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow :=
      cokernel.π_desc _ _ _
    -- Kernel square in truncatedUnderlyingComplex terms
    have h_ker_sq : compat_s ≫
        (((truncatedUnderlyingComplex cm s₀ t).fil s 1).arrow ≫
          (truncatedUnderlyingComplex cm s₀ t).d 1 ≫
          cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow) =
        (((truncatedUnderlyingComplex cm s₁ t).fil s 1).arrow ≫
          (truncatedUnderlyingComplex cm s₁ t).d 1 ≫
          cokernel.π ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow) ≫
        cok_right := by sorry

    exact imageSubobjectMap_of_kernel_cokernel_square h_ker_sq h_πV_comm

private lemma factor_through_inf {X Y : C} {P Q : Subobject Y}
    (f : X ⟶ Y)
    (hP : P.Factors f) (hQ : Q.Factors f) :
    (P ⊓ Q).Factors f := by
  rw [Subobject.inf_factors]; exact ⟨hP, hQ⟩

private theorem truncatedUC_boundarySubobject_zero_preserved
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (t : ω') (s : ℤ) (r : WithTop ℕ) :
    ∃ (lift : Subobject.underlying.obj
          ((truncatedUnderlyingComplex cm s₁ t).boundarySubobject s 0 r) ⟶
        Subobject.underlying.obj
          ((truncatedUnderlyingComplex cm s₀ t).boundarySubobject s 0 r)),
      lift ≫ ((truncatedUnderlyingComplex cm s₀ t).boundarySubobject s 0 r).arrow =
        ((truncatedUnderlyingComplex cm s₁ t).boundarySubobject s 0 r).arrow ≫
          (eqToHom (truncatedUC_assocGraded_zero cm s₁ t s) ≫
            Filtration.inducedAssocGradedMap
              (fun k' => F₂.truncationTransition h k')
              (fun s' k' => truncationTransition_fil_compat₂ h s' k')
              s t ≫
            eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm) := by
  -- Abbreviation for the graded map φ
  set grφ := eqToHom (truncatedUC_assocGraded_zero cm s₁ t s) ≫
    Filtration.inducedAssocGradedMap
      (fun k' => F₂.truncationTransition h k')
      (fun s' k' => truncationTransition_fil_compat₂ h s' k')
      s t ≫
    eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm with hgrφ_def
  -- Strip eqToHom wrappers from grφ (must be BEFORE set FC₀/FC₁)
  have h_grφ_simp : grφ =
      Filtration.inducedAssocGradedMap
        (fun k' => F₂.truncationTransition h k')
        (fun s' k' => truncationTransition_fil_compat₂ h s' k')
        s t := by
    simp only [grφ, truncatedUnderlyingComplex, underlyingComplex,
      FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- The filtration compat lift at s (for the cokernel = assocGraded)
  -- Use .choose so it matches what inducedAssocGradedMap uses internally
  set lift_s := (truncationTransition_fil_compat₂ (F₂ := F₂) h s t).choose
  have hlift_s_spec := (truncationTransition_fil_compat₂ (F₂ := F₂) h s t).choose_spec
  -- Naturality of dToK 0 w.r.t. the truncation transition
  have h_dToK_nat : F₁.truncationTransition h t ≫
      (truncatedUnderlyingComplex cm s₀ t).dToK 0 =
      (truncatedUnderlyingComplex cm s₁ t).dToK 0 ≫
        F₂.truncationTransition h t := by
    simp only [FilteredComplex.dToK, truncatedUnderlyingComplex,
      underlyingComplex, twoTermDiff, twoTermObj]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact truncatedAMap_naturality cm h t
  -- Abbreviate the filtered complexes (use let, not set, to preserve grφ as let-binding)
  let FC₀ := truncatedUnderlyingComplex cm s₀ t
  let FC₁ := truncatedUnderlyingComplex cm s₁ t
  -- Case split on r
  cases r with
  | top =>
    set I₀ := imageSubobject (FC₀.dToK 0) ⊓ FC₀.fil s 0
    set I₁ := imageSubobject (FC₁.dToK 0) ⊓ FC₁.fil s 0
    -- Step 1: Prove I₀.Factors (I₁.arrow ≫ τ₂) using factorThru (not ofLE)
    -- For the imageSubobject factor:
    have h_fac_imgD₁ : (imageSubobject (FC₁.dToK 0)).Factors I₁.arrow :=
      Subobject.inf_arrow_factors_left _ _
    have h_imgD_map := imageSubobjectMap_arrow
      (Arrow.homMk' (F₁.truncationTransition h t)
        (F₂.truncationTransition h t) h_dToK_nat)
    have h_fac_imgD₀ : (imageSubobject (FC₀.dToK 0)).Factors
        (I₁.arrow ≫ F₂.truncationTransition h t) := by
      -- Rewrite I₁.arrow as factorThru ≫ imgD₁.arrow
      rw [← Subobject.factorThru_arrow _ _ h_fac_imgD₁, Category.assoc]
      -- Now goal: imgD₀.Factors (factorThru ≫ imgD₁.arrow ≫ τ₂)
      -- Use h_imgD_map: imgMap ≫ imgD₀.arrow = imgD₁.arrow ≫ Arrow.homMk'(...).right
      -- Arrow.homMk'(...).right = τ₂
      simp only [Arrow.homMk'] at h_imgD_map
      rw [← h_imgD_map]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    -- For the filtration factor:
    have h_fac_fil₁ : (FC₁.fil s 0).Factors I₁.arrow :=
      Subobject.inf_arrow_factors_right _ _
    have h_fac_fil₀ : (FC₀.fil s 0).Factors
        (I₁.arrow ≫ F₂.truncationTransition h t) := by
      rw [← Subobject.factorThru_arrow _ _ h_fac_fil₁, Category.assoc]
      show (FC₀.fil s 0).Factors
          ((FC₁.fil s 0).factorThru I₁.arrow h_fac_fil₁ ≫
            ((F₂.truncatedFiltration s₁).F s t).arrow ≫ F₂.truncationTransition h t)
      rw [← hlift_s_spec]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    have h_fac_I : I₀.Factors (I₁.arrow ≫ F₂.truncationTransition h t) :=
      factor_through_inf _ h_fac_imgD₀ h_fac_fil₀
    -- Step 2: Build α
    set α := I₀.factorThru _ h_fac_I
    have hα := I₀.factorThru_arrow _ h_fac_I
    -- Step 3: Prove the comm square for the boundary map
    -- boundarySubobject uses ofLE I (FC.fil s 0) inf_le_right ≫ cokernel.π ι
    set ι₀ := Subobject.ofLE (FC₀.fil (s + 1) 0) (FC₀.fil s 0) (FC₀.fil_anti s 0)
    set ι₁ := Subobject.ofLE (FC₁.fil (s + 1) 0) (FC₁.fil s 0) (FC₁.fil_anti s 0)
    have h_sq_comm : α ≫ (Subobject.ofLE I₀ (FC₀.fil s 0) inf_le_right ≫ cokernel.π ι₀) =
        (Subobject.ofLE I₁ (FC₁.fil s 0) inf_le_right ≫ cokernel.π ι₁) ≫ grφ := by
      -- Use cancel_mono to reduce to an equation about arrows
      -- First, rewrite ofLE ≫ arrow = arrow
      have h_ofLE₀ := Subobject.ofLE_arrow (X := I₀) (Y := FC₀.fil s 0) inf_le_right
      have h_ofLE₁ := Subobject.ofLE_arrow (X := I₁) (Y := FC₁.fil s 0) inf_le_right
      -- We need: α ≫ ofLE ≫ πV = ofLE ≫ πV ≫ grφ
      -- Strategy: show both sides, after composing with (FC₀.fil s 0).arrow, are equal,
      -- then use the cokernel exactness to conclude.
      -- Actually, let's use the known equation:
      -- h_lift_πV (after establishing it): lift_s ≫ πV₀ = πV₁ ≫ grφ
      -- And: α ≫ ofLE₀ ≫ (FC₀.fil s 0).arrow = α ≫ I₀.arrow (by ofLE_arrow)
      --     = I₁.arrow ≫ τ₂ (by hα)
      --     = ofLE₁ ≫ (FC₁.fil s 0).arrow ≫ τ₂ (by ofLE_arrow)
      --     = ofLE₁ ≫ lift_s ≫ (FC₀.fil s 0).arrow (by hlift_s_spec.symm... type issue)
      -- This shows: α ≫ ofLE₀ = ofLE₁ ≫ lift_s (after cancel_mono)
      -- Then: α ≫ ofLE₀ ≫ πV₀ = ofLE₁ ≫ lift_s ≫ πV₀ = ofLE₁ ≫ πV₁ ≫ grφ
      -- Intermediate: α ≫ ofLE₀ = ofLE₁ ≫ lift_s
      have hlift_FC : lift_s ≫ (FC₀.fil s 0).arrow =
          (FC₁.fil s 0).arrow ≫ F₂.truncationTransition h t := hlift_s_spec
      have h_mid : α ≫ Subobject.ofLE I₀ (FC₀.fil s 0) inf_le_right =
          Subobject.ofLE I₁ (FC₁.fil s 0) inf_le_right ≫ lift_s := by
        apply (cancel_mono (FC₀.fil s 0).arrow).mp
        simp only [Category.assoc]
        rw [h_ofLE₀, hα, hlift_FC, ← Category.assoc, h_ofLE₁]
      rw [← Category.assoc, h_mid, Category.assoc]
      -- Now goal: ofLE₁ ≫ lift_s ≫ πV₀ = (ofLE₁ ≫ πV₁) ≫ grφ
      rw [Category.assoc]
      congr 1
      -- Goal: lift_s ≫ πV₀ = πV₁ ≫ grφ
      -- This needs h_lift_πV, but we need to match types.
      -- πV₀ = cokernel.π ι₀ where ι₀ uses FC₀ types
      -- h_lift_πV needs πV with truncatedFiltration types
      -- Use show/change to normalize
      show lift_s ≫ cokernel.π (Subobject.ofLE
            ((F₂.truncatedFiltration s₀).F (s + 1) t)
            ((F₂.truncatedFiltration s₀).F s t)
            ((F₂.truncatedFiltration s₀).mono s t)) =
          cokernel.π (Subobject.ofLE
            ((F₂.truncatedFiltration s₁).F (s + 1) t)
            ((F₂.truncatedFiltration s₁).F s t)
            ((F₂.truncatedFiltration s₁).mono s t)) ≫ grφ
      rw [h_grφ_simp]
      simp only [Filtration.inducedAssocGradedMap]
      rw [cokernel.π_desc]
    -- Step 4: Conclude
    delta FilteredComplex.boundarySubobject
    exact ⟨imageSubobjectMap (Arrow.homMk' α grφ h_sq_comm),
           imageSubobjectMap_arrow (Arrow.homMk' α grφ h_sq_comm)⟩
  | coe n =>
    sorry


noncomputable def truncatedESSTransition
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (t : ω') :
    SpectralSequenceMorphism (truncatedESS cm hbb₁ hbb₂ s₁ t)
      (truncatedESS cm hbb₁ hbb₂ s₀ t) where
  φ := fun ⟨s, k⟩ => by
    change (truncatedUnderlyingComplex cm s₁ t).assocGraded s k ⟶
           (truncatedUnderlyingComplex cm s₀ t).assocGraded s k
    by_cases h₁ : k = 1
    · subst h₁
      exact eqToHom (truncatedUC_assocGraded_one cm s₁ t s) ≫
        Filtration.inducedAssocGradedMap
          (fun k' => F₁.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₁ h s' k')
          s t ≫
        eqToHom (truncatedUC_assocGraded_one cm s₀ t s).symm
    · by_cases h₀ : k = 0
      · subst h₀
        exact eqToHom (truncatedUC_assocGraded_zero cm s₁ t s) ≫
          Filtration.inducedAssocGradedMap
            (fun k' => F₂.truncationTransition h k')
            (fun s' k' => truncationTransition_fil_compat₂ h s' k')
            s t ≫
          eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm
      · exact 0
  preserves_Z := fun ⟨s, k⟩ r => by
    by_cases h₁ : k = 1
    · subst h₁
      simp only [↓reduceDIte]
      exact truncatedUC_cycleSubobject_one_preserved cm hbb₁ hbb₂ h t s r
    · by_cases h₀ : k = 0
      · subst h₀
        simp only [↓reduceDIte]
        have hZ₀_top : (((truncatedESS cm hbb₁ hbb₂ s₀ t).ssData (s, 0)).Z r) = ⊤ := by
          show (truncatedUnderlyingComplex cm s₀ t).cycleSubobject s 0 r = ⊤
          exact truncatedUC_cycleSubobject_zero_eq_top cm s₀ t s r
        have hfac : (((truncatedESS cm hbb₁ hbb₂ s₀ t).ssData (s, 0)).Z r).Factors
            ((((truncatedESS cm hbb₁ hbb₂ s₁ t).ssData (s, 0)).Z r).arrow ≫
              (eqToHom (truncatedUC_assocGraded_zero cm s₁ t s) ≫
                Filtration.inducedAssocGradedMap
                  (fun k' => F₂.truncationTransition h k')
                  (fun s' k' => truncationTransition_fil_compat₂ h s' k')
                  s t ≫
                eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm)) := by
          rw [hZ₀_top]; exact Subobject.top_factors _
        exact ⟨(((truncatedESS cm hbb₁ hbb₂ s₀ t).ssData (s, 0)).Z r).factorThru
            _ hfac,
          (((truncatedESS cm hbb₁ hbb₂ s₀ t).ssData (s, 0)).Z r).factorThru_arrow
            _ hfac⟩
      · exact ⟨0, by simp [dif_neg h₁, dif_neg h₀]⟩
  preserves_B := fun ⟨s, k⟩ r => by
    by_cases h₁ : k = 1
    · subst h₁
      simp only [↓reduceDIte]
      refine ⟨0, ?_⟩
      have h1 : (((truncatedESS cm hbb₁ hbb₂ s₁ t).ssData (s, 1)).B r).arrow = 0 := by
        show ((truncatedUnderlyingComplex cm s₁ t).boundarySubobject s 1 r).arrow = 0
        rw [truncatedUC_boundarySubobject_one_eq_bot cm s₁ t s r, Subobject.bot_arrow]
      simp [h1, zero_comp]
    · by_cases h₀ : k = 0
      · subst h₀
        simp only [↓reduceDIte, id]
        have h₁' : (0 : ℤ) ≠ 1 := by omega
        simp only [dif_neg h₁']
        exact truncatedUC_boundarySubobject_zero_preserved cm hbb₁ hbb₂ h t s r
      · exact ⟨0, by simp [dif_neg h₁, dif_neg h₀]⟩
  comm_d := fun r ⟨s, k⟩ => by
    by_cases h₁ : k = 1
    · subst h₁
      exact ⟨0, 0, by simp [comp_zero, zero_comp]⟩
    · by_cases h₀ : k = 0
      · subst h₀
        exact ⟨0, 0, by simp [comp_zero, zero_comp]⟩
      · -- k ≠ 0, 1: all differentials are zero
        exact ⟨0, 0, by simp [comp_zero, zero_comp]⟩

/-! ### Section 3: Stabilization -/

theorem truncatedESS_pageStabilization
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (sk : ℤ × ℤ) (r : ℤ) :
    ∃ s₀_min : ℤ, ∀ s₀ ≥ s₀_min,
      Nonempty ((truncatedESS cm hbb₁ hbb₂ s₀ t).Page r sk ≅
        (truncatedESS cm hbb₁ hbb₂ s₀_min t).Page r sk) :=
  sorry

/-! ### Section 4: Unbounded extension spectral sequence -/

noncomputable def UnboundedExtensionSS
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  sorry

theorem UnboundedExtensionSS.pageIso
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (sk : ℤ × ℤ) (r : ℤ) :
    ∃ s₀_min : ℤ, ∀ s₀ ≥ s₀_min,
      Nonempty ((UnboundedExtensionSS cm hbb₁ hbb₂ t).Page r sk ≅
        (truncatedESS cm hbb₁ hbb₂ s₀ t).Page r sk) :=
  sorry

/-! ### Section 5: Convergence -/

axiom UnboundedExtensionSS.weakConvergence
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (hml₁ : F₁.IsMittagLeffler) (hml₂ : F₂.IsMittagLeffler) (t : ω') :
    ∃ (complexCompletion : FilteredComplex C),
      Nonempty (Convergence (UnboundedExtensionSS cm hbb₁ hbb₂ t)
        complexCompletion.homologyObj complexCompletion.homologyFiltration)

end KIPBase.SpectralSequence
