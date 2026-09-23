import KIP126.Def.SpectralSequence.FilteredPage.Data
import KIP126.Def.SpectralSequence.Basic.Data

/-!
# Order laws for filtered-complex pages

These are the mathematical laws formerly bundled in KIPBase's `toSSData`,
proved for the canonical filtered complex. The page quotient is a construction
from its subobjects; Mathlib remains the spectral-sequence type.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The Z_anti law for the canonical page subobjects. -/
theorem cycleSubobject_antitone (FC : FilteredComplex C) (s k : ℤ) :
    Antitone (FC.cycleSubobject s k) := by
  intro r₁ r₂ hr₁₂
  suffices key : ∀ {X Y : C} {K₁ K₂ : Subobject X} (g : X ⟶ Y)
      (hle : K₂ ≤ K₁),
      imageSubobject (K₂.arrow ≫ g) ≤ imageSubobject (K₁.arrow ≫ g) by
    rcases r₁ with _ | n₁ <;> rcases r₂ with _ | n₂
    · -- (⊤, ⊤)
      exact le_refl _
    · -- (⊤, ↑n₂): impossible
      exact absurd hr₁₂ (WithTop.not_top_le_coe n₂)
    · -- (↑n₁, ⊤): ker(arrow ≫ d) ≤ ker(arrow ≫ d ≫ cokernel.π)
      change imageSubobject
          ((kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))).arrow ≫ _) ≤
        imageSubobject
          ((kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
            cokernel.π ((FC.filtration.F (s + ↑n₁) (k - 1)).arrow))).arrow ≫ _)
      apply key
      apply le_kernelSubobject
      have h1 : (kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))).arrow ≫
          ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) = 0 := kernelSubobject_arrow_comp _
      calc (kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))).arrow ≫
              ((FC.filtration.F s k).arrow ≫ (FC.complex.d k (k - 1) ≫
                cokernel.π ((FC.filtration.F (s + ↑n₁) (k - 1)).arrow)))
          = ((kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))).arrow ≫
              (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑n₁) (k - 1)).arrow) := by
              simp only [Category.assoc]
        _ = 0 ≫ cokernel.π ((FC.filtration.F (s + ↑n₁) (k - 1)).arrow) := by rw [h1]
        _ = 0 := zero_comp
    · -- (↑n₁, ↑n₂): n₁ ≤ n₂
      change imageSubobject
          ((kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
            cokernel.π ((FC.filtration.F (s + ↑n₂) (k - 1)).arrow))).arrow ≫ _) ≤
        imageSubobject
          ((kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
            cokernel.π ((FC.filtration.F (s + ↑n₁) (k - 1)).arrow))).arrow ≫ _)
      have hn : n₁ ≤ n₂ := WithTop.coe_le_coe.mp hr₁₂
      have hfil : FC.filtration.F (s + ↑n₂) (k - 1) ≤ FC.filtration.F (s + ↑n₁) (k - 1) :=
        FC.filtration.le_of_le (by omega) (k - 1)
      have hcomp : (FC.filtration.F (s + ↑n₂) (k - 1)).arrow ≫
          cokernel.π ((FC.filtration.F (s + ↑n₁) (k - 1)).arrow) = 0 := by
        rw [show (FC.filtration.F (s + ↑n₂) (k - 1)).arrow =
          Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n₁) (k - 1)).arrow
          from (Subobject.ofLE_arrow hfil).symm]
        rw [Category.assoc, cokernel.condition, comp_zero]
      set f_n₂ := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
        cokernel.π ((FC.filtration.F (s + ↑n₂) (k - 1)).arrow) with hf_n₂_def
      set f_n₁ := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
        cokernel.π ((FC.filtration.F (s + ↑n₁) (k - 1)).arrow) with hf_n₁_def
      have hker : kernelSubobject f_n₂ ≤ kernelSubobject f_n₁ := by
        apply le_kernelSubobject
        set desc := cokernel.desc ((FC.filtration.F (s + ↑n₂) (k - 1)).arrow)
          (cokernel.π ((FC.filtration.F (s + ↑n₁) (k - 1)).arrow)) hcomp
        have hfactor : f_n₁ = f_n₂ ≫ desc := by
          simp only [f_n₂, f_n₁, desc, Category.assoc, cokernel.π_desc]
        rw [hfactor, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
      exact key _ hker
  intro X Y K₁ K₂ g hle
  rw [show K₂.arrow ≫ g = Subobject.ofLE K₂ K₁ hle ≫ K₁.arrow ≫ g by
    rw [← Category.assoc, Subobject.ofLE_arrow]]
  exact imageSubobject_comp_le _ _

/-- The B_mono law for the canonical page subobjects. -/
theorem boundarySubobject_monotone (FC : FilteredComplex C) (s k : ℤ) :
    Monotone (FC.boundarySubobject s k) := by
  intro r₁ r₂ hr₁₂
  suffices img_mono : ∀ {X Y : C} {K₁ K₂ : Subobject X} (g : X ⟶ Y)
      (hle : K₁ ≤ K₂),
      imageSubobject (K₁.arrow ≫ g) ≤ imageSubobject (K₂.arrow ≫ g) by
    have ofLE_mono : ∀ {X Y : C} {I₁ I₂ Q : Subobject X}
        (h₁ : I₁ ≤ Q) (h₂ : I₂ ≤ Q) (hle : I₁ ≤ I₂)
        (g : Subobject.underlying.obj Q ⟶ Y),
        imageSubobject (Subobject.ofLE I₁ Q h₁ ≫ g) ≤
        imageSubobject (Subobject.ofLE I₂ Q h₂ ≫ g) := by
      intro X Y I₁ I₂ Q h₁ h₂ hle g
      have factored : Subobject.ofLE I₁ Q h₁ =
          Subobject.ofLE I₁ I₂ hle ≫ Subobject.ofLE I₂ Q h₂ := by
        apply (cancel_mono Q.arrow).mp
        simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [factored, Category.assoc]
      exact imageSubobject_comp_le _ _
    simp only [FilteredComplex.boundarySubobject]
    rcases r₁ with _ | n₁ <;> rcases r₂ with _ | n₂
    · exact le_refl _
    · exact absurd hr₁₂ (WithTop.not_top_le_coe n₂)
    · -- (↑n₁, ⊤): image from F^{s-n₁} ≤ image from all of A^{k+1}
      apply ofLE_mono inf_le_right inf_le_right
      apply inf_le_inf_right
      exact imageSubobject_comp_le _ _
    · -- (↑n₁, ↑n₂): F^{s-n₁+1} ≤ F^{s-n₂+1} (since n₁ ≤ n₂, s-n₂+1 ≤ s-n₁+1)
      have hn : n₁ ≤ n₂ := WithTop.coe_le_coe.mp hr₁₂
      have hfil : FC.filtration.F (s - ↑n₁ + 1) (k + 1) ≤ FC.filtration.F (s - ↑n₂ + 1) (k + 1) :=
        FC.filtration.le_of_le (by omega) (k + 1)
      apply ofLE_mono inf_le_right inf_le_right
      apply inf_le_inf_right
      exact img_mono _ hfil
  intro X Y K₁ K₂ g hle
  rw [show K₁.arrow ≫ g = Subobject.ofLE K₁ K₂ hle ≫ K₂.arrow ≫ g by
    rw [← Category.assoc, Subobject.ofLE_arrow]]
  exact imageSubobject_comp_le _ _

/-- The Z_zero law for the canonical page subobjects. -/
theorem cycleSubobject_zero (FC : FilteredComplex C) (s k : ℤ) :
    FC.cycleSubobject s k 0 = ⊤ := by
  simp only [FilteredComplex.cycleSubobject]
  have hf0 : (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑(0 : ℕ)) (k - 1)).arrow) = 0 := by
    obtain ⟨φ, hφ⟩ := FC.differential_preserves s k
    simp only [← Category.assoc]
    rw [← hφ]
    simp only [Category.assoc]
    have hle : FC.filtration.F s (k - 1) ≤ FC.filtration.F (s + ↑(0 : ℕ)) (k - 1) :=
      le_of_eq (by congr 1; omega)
    rw [show (FC.filtration.F s (k - 1)).arrow =
      Subobject.ofLE (FC.filtration.F s (k - 1)) (FC.filtration.F (s + ↑(0 : ℕ)) (k - 1)) hle ≫
      (FC.filtration.F (s + ↑(0 : ℕ)) (k - 1)).arrow from (Subobject.ofLE_arrow hle).symm]
    simp only [Category.assoc, cokernel.condition, comp_zero]
  haveI : IsIso (kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑(0 : ℕ)) (k - 1)).arrow))).arrow := by
    rw [Subobject.isIso_arrow_iff_eq_top]
    simp only [hf0, kernelSubobject_zero]
  rw [imageSubobject_iso_comp]
  let π := cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) k)
    (FC.filtration.F s k) (FC.filtration.decreasing s k))
  haveI : Epi (image.ι π) := epi_image_of_epi _
  haveI : IsIso (image.ι π) := isIso_of_mono_of_epi _
  haveI : IsIso (imageSubobject π).arrow := by
    have h : IsIso ((imageSubobjectIso π).hom ≫ image.ι π) := inferInstance
    rw [imageSubobject_arrow] at h
    exact h
  apply (Subobject.isIso_arrow_iff_eq_top _).mp
  change IsIso (imageSubobject π).arrow
  infer_instance

/-- The Z_top_greatest endpoint law under the corresponding filtration bound. -/
theorem cycleSubobject_top_greatest (FC : FilteredComplex C)
    (bnd : FC.filtration.IsBoundedAbove) (s k : ℤ)
    (X : Subobject (FC.filtration.associatedGraded s k))
    (hX : ∀ i : ℕ, X ≤ FC.cycleSubobject s k ↑i) :
    X ≤ FC.cycleSubobject s k ⊤ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, FC.filtration.F (s + ↑N) (k - 1) = ⊥ := by
    use (bnd.upper (k - 1) - s).toNat
    apply bnd.eq_bot_of_le; omega
  have h_zero : (FC.filtration.F (s + ↑N) (k - 1)).arrow = 0 := by
    rw [hN, Subobject.bot_arrow]
  haveI : IsIso (cokernel.π ((FC.filtration.F (s + ↑N) (k - 1)).arrow)) := by
    rw [h_zero]; exact cokernel.π_zero_isIso
  have hle : kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑N) (k - 1)).arrow)) ≤
    kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) := by
    apply le_kernelSubobject
    have h1 := kernelSubobject_arrow_comp ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
        cokernel.π ((FC.filtration.F (s + ↑N) (k - 1)).arrow))
    rw [← cancel_mono (cokernel.π ((FC.filtration.F (s + ↑N) (k - 1)).arrow))]
    simp only [Category.assoc, zero_comp]
    exact h1
  have hle' : kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑(↑N : ℕ)) (k - 1)).arrow)) ≤
    kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) := hle
  suffices hsuff : FC.cycleSubobject s k ↑N ≤ FC.cycleSubobject s k ⊤ from
    le_trans (hX N) hsuff
  change imageSubobject
      ((kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
        cokernel.π ((FC.filtration.F (s + ↑N) (k - 1)).arrow))).arrow ≫
        cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k))) ≤
    imageSubobject
      ((kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))).arrow ≫
        cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k)))
  have heq : (kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑N) (k - 1)).arrow))).arrow ≫
      cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k)) =
    Subobject.ofLE _ _ hle ≫ (kernelSubobject ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))).arrow ≫
      cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k)) := by
    conv_rhs => rw [← Category.assoc]
    congr 1
    exact (Subobject.ofLE_arrow hle).symm
  rw [heq]
  exact imageSubobject_comp_le _ _

/-- The B_top_least endpoint law under the corresponding filtration bound. -/
theorem boundarySubobject_top_least (FC : FilteredComplex C)
    (bnd : FC.filtration.IsBoundedBelow) (s k : ℤ)
    (X : Subobject (FC.filtration.associatedGraded s k))
    (hX : ∀ i : ℕ, FC.boundarySubobject s k ↑i ≤ X) :
    FC.boundarySubobject s k ⊤ ≤ X := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, FC.filtration.F (s - ↑N + 1) (k + 1) = ⊤ := by
    use (s + 1 - bnd.lower (k + 1)).toNat
    apply bnd.eq_top_of_le; omega
  haveI : IsIso (FC.filtration.F (s - ↑N + 1) (k + 1)).arrow := by
    rw [Subobject.isIso_arrow_iff_eq_top]; exact hN
  have himgD : imageSubobject ((FC.filtration.F (s - ↑N + 1) (k + 1)).arrow ≫ FC.dToK k) =
      imageSubobject (FC.dToK k) :=
    imageSubobject_iso_comp _ _
  suffices hsuff : FC.boundarySubobject s k ⊤ ≤ FC.boundarySubobject s k ↑N from
    le_trans hsuff (hX N)
  change imageSubobject (Subobject.ofLE (imageSubobject (FC.dToK k) ⊓ FC.filtration.F s k)
        (FC.filtration.F s k) inf_le_right ≫
        cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k))) ≤
    imageSubobject (Subobject.ofLE
        (imageSubobject ((FC.filtration.F (s - ↑N + 1) (k + 1)).arrow ≫ FC.dToK k) ⊓ FC.filtration.F s k)
        (FC.filtration.F s k) inf_le_right ≫
        cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k)))
  rw [himgD]

/-! ### Basic quotient-page consequences

These are the canonical-page counterparts of the elementary `SSData` laws in
the historical spectral-sequence API.  They use the existing cycle/boundary
subobjects and `pageObj`; no second page-data structure is introduced. -/

/-- Every boundary at the bottom page is contained in every cycle subobject. -/
theorem boundarySubobject_bot_le_cycle (FC : FilteredComplex C) (s k : ℤ)
    (r : WithTop ℕ) :
    FC.boundarySubobject s k ⊥ ≤ FC.cycleSubobject s k r := by
  exact le_trans (boundarySubobject_monotone FC s k bot_le)
    (FC.B_le_Z_aux s k r)

/-- If the boundary and cycle subobjects coincide, the quotient page vanishes. -/
theorem pageObj_isZero_of_eq (FC : FilteredComplex C) (s k : ℤ)
    (r : WithTop ℕ) (h : FC.boundarySubobject s k r = FC.cycleSubobject s k r) :
    IsZero (FC.pageObj s k r) := by
  unfold pageObj
  have hi : IsIso (Subobject.ofLE (FC.boundarySubobject s k r)
      (FC.cycleSubobject s k r) (FC.B_le_Z_aux s k r)) := by
    rw [← Subobject.isoOfEq_hom _ _ h]
    infer_instance
  exact isZero_cokernel_of_epi _

/-- A zero quotient page forces its boundary and cycle subobjects to coincide. -/
theorem eq_of_pageObj_isZero (FC : FilteredComplex C) (s k : ℤ)
    (r : WithTop ℕ) (h : IsZero (FC.pageObj s k r)) :
    FC.boundarySubobject s k r = FC.cycleSubobject s k r := by
  unfold pageObj at h
  have hepi : Epi (Subobject.ofLE (FC.boundarySubobject s k r)
      (FC.cycleSubobject s k r) (FC.B_le_Z_aux s k r)) := by
    rwa [Preadditive.epi_iff_isZero_cokernel]
  haveI : IsIso (Subobject.ofLE (FC.boundarySubobject s k r)
      (FC.cycleSubobject s k r) (FC.B_le_Z_aux s k r)) :=
    isIso_of_mono_of_epi _
  apply le_antisymm (FC.B_le_Z_aux s k r)
  exact Subobject.le_of_comm
    (inv (Subobject.ofLE (FC.boundarySubobject s k r)
      (FC.cycleSubobject s k r) (FC.B_le_Z_aux s k r)))
    (by simp [Subobject.ofLE_arrow])

/-- The canonical page is zero exactly when its boundary and cycle subobjects agree. -/
theorem pageObj_isZero_iff (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ) :
    IsZero (FC.pageObj s k r) ↔
      FC.boundarySubobject s k r = FC.cycleSubobject s k r := by
  constructor
  · exact eq_of_pageObj_isZero FC s k r
  · exact pageObj_isZero_of_eq FC s k r

/-! ### Quotient maps for nested subobjects

These constructions are the categorical quotient tools used by the historical
page-homology argument. They are stated independently of any spectral-sequence
record and therefore remain reusable with the canonical `pageObj` quotient. -/

/-- The quotient map induced by `P ≤ Q ≤ R`: `R/P ⟶ R/Q`. -/
noncomputable def Subobject.cokernelDescOfLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P R hPR) ⟶ cokernel (Subobject.ofLE Q R hQR) :=
  Subobject.cokernelDesc_ofLE P Q R hPQ hQR hPR

/-- The map induced by `P ≤ Q ≤ R`: `Q/P ⟶ R/P`. -/
noncomputable def Subobject.cokernelMapOfLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P Q hPQ) ⟶ cokernel (Subobject.ofLE P R hPR) :=
  Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR

/-- The third-isomorphism identification `(R/P)/(Q/P) ≅ R/Q`. -/
noncomputable def Subobject.thirdQuotientIso {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.cokernelMapOfLE P Q R hPQ hQR hPR) ≅
      cokernel (Subobject.ofLE Q R hQR) :=
  Subobject.thirdIso P Q R hPQ hQR hPR

end KIP126.Core.SpectralSequence.FilteredComplex
