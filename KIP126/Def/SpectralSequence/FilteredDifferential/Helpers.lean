import Mathlib.CategoryTheory.Abelian.Exact
import KIP126.Def.SpectralSequence.FilteredDifferential.Data

/-! Kernel, image, and transport lemmas used by finite-page differential proofs. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DifferentialHelpers

theorem kernelSubobject_epiDesc' {C' : Type*} [Category C'] [Abelian C']
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


theorem kernelSubobject_cokernel_desc' {C' : Type*} [Category C'] [Abelian C']
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

theorem eqToHom_arrow_dToK_gen_local (FC : FilteredComplex C)
    (s : ℤ) (m k : ℤ) (hmk : m + 1 = k) :
    eqToHom (show Subobject.underlying.obj (FC.filtration.F s k) =
      Subobject.underlying.obj (FC.filtration.F s (m + 1)) by rw [hmk]) ≫
    ((FC.filtration.F s (m + 1)).arrow ≫ FC.dToK m) =
      (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      eqToHom (congr_arg FC.complex.X (show k - 1 = m by omega)) := by
  subst hmk
  simp [FilteredComplex.dToK]

theorem eqToHom_arrow_dToK_local (FC : FilteredComplex C)
    (s k : ℤ) :
    eqToHom (show Subobject.underlying.obj (FC.filtration.F s k) =
      Subobject.underlying.obj (FC.filtration.F s ((k - 1) + 1)) by
      rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
    ((FC.filtration.F s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
      (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
  rw [eqToHom_arrow_dToK_gen_local FC s (k - 1) k (by omega)]
  simp

lemma imageSubobject_epi_comp'_local {C' : Type*} [Category C'] [Abelian C']
    {X₁ X₂ X₃ : C'} (e : X₁ ⟶ X₂) [Epi e] (f : X₂ ⟶ X₃) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
    (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm)

end DifferentialHelpers

end KIP126.Core.SpectralSequence.FilteredComplex
