import KIP126.Def.SpectralSequence.FilteredPage.Complex
import Mathlib.CategoryTheory.Abelian.Pseudoelements

/-! Adjacent-page homology and assembly of the canonical finite quotient pages. -/
namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma imageSubobject_epi_comp {X₁ X₂ X₃ : C}
    (e : X₁ ⟶ X₂) [Epi e] (f : X₂ ⟶ X₃) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
    (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm)

private lemma comp_eq_zero_of_image_le_kernel {X₁ X₂ X₃ : C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (h : imageSubobject f ≤ kernelSubobject g) : f ≫ g = 0 := by
  rw [← imageSubobject_arrow_comp f, Category.assoc,
    show (imageSubobject f).arrow =
        Subobject.ofLE _ _ h ≫ (kernelSubobject g).arrow
      from (Subobject.ofLE_arrow h).symm,
    Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]

private lemma factor_cokernelMap {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) =
      cokernel.π (Subobject.ofLE P Q hPQ) ≫
        Subobject.cokernelMapOfLE P Q R hPQ hQR hPR := by
  simp [Subobject.cokernelMapOfLE, Subobject.cokernelMap_ofLE, cokernel.π_desc]

private instance cokernelMapOfLE_mono {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    Mono (Subobject.cokernelMapOfLE P Q R hPQ hQR hPR) := by
  open CategoryTheory.Abelian.Pseudoelement in
  refine mono_of_zero_of_map_zero _ fun a ha => ?_
  obtain ⟨q, hq⟩ :=
    pseudo_surjective_of_epi (cokernel.π (Subobject.ofLE P Q hPQ)) a
  rw [← hq] at ha ⊢
  have ha' :
      pseudoApply (cokernel.π (Subobject.ofLE P R hPR))
        (pseudoApply (Subobject.ofLE Q R hQR) q) = 0 := by
    have h1 := (Abelian.Pseudoelement.comp_apply
      (Subobject.ofLE Q R hQR)
      (cokernel.π (Subobject.ofLE P R hPR)) q).symm
    rw [h1, factor_cokernelMap P Q R hPQ hQR hPR,
      Abelian.Pseudoelement.comp_apply]
    exact ha
  have hexact :
      (ShortComplex.mk (Subobject.ofLE P R hPR)
        (cokernel.π (Subobject.ofLE P R hPR))
        (cokernel.condition _)).Exact :=
    ShortComplex.cokernelSequence_exact (Subobject.ofLE P R hPR)
  obtain ⟨p, hp⟩ := pseudo_exact_of_exact hexact _ ha'
  have hp' :
      pseudoApply (Subobject.ofLE Q R hQR)
          (pseudoApply (Subobject.ofLE P Q hPQ) p) =
        pseudoApply (Subobject.ofLE Q R hQR) q := by
    rw [← Abelian.Pseudoelement.comp_apply, Subobject.ofLE_comp_ofLE]
    exact hp
  have hinj := pseudo_injective_of_mono (Subobject.ofLE Q R hQR) hp'
  rw [← hinj, ← Abelian.Pseudoelement.comp_apply,
    cokernel.condition, zero_apply]

/-- The categorical third-isomorphism argument used in every adjacent-page
comparison.  If `P ≤ Q ≤ R ≤ U`, the middle term is `U/P`, the kernel of the
outgoing map is the image of `R/P`, and the image of the incoming map is the
image of `Q/P`; hence the homology is `R/Q`. -/
private noncomputable def nestedSubobjectHomologyIso {V : C}
    (P Q R U : Subobject V)
    (hPQ : P ≤ Q) (hQR : Q ≤ R) (hRU : R ≤ U)
    (hPR : P ≤ R) (hPU : P ≤ U) (hQU : Q ≤ U)
    {X₁ X₃ : C}
    (f : X₁ ⟶ cokernel (Subobject.ofLE P U hPU))
    (g : cokernel (Subobject.ofLE P U hPU) ⟶ X₃)
    (zero : f ≫ g = 0)
    (hker : kernelSubobject g =
      imageSubobject (Subobject.ofLE R U hRU ≫
        cokernel.π (Subobject.ofLE P U hPU)))
    (himg : imageSubobject f =
      imageSubobject (Subobject.ofLE Q U hQU ≫
        cokernel.π (Subobject.ofLE P U hPU))) :
    (ShortComplex.mk f g zero).homology ≅
      cokernel (Subobject.ofLE Q R hQR) := by
  let i := Subobject.cokernelMapOfLE P R U hPR hRU hPU
  let πMap := Subobject.cokernelDescOfLE P Q R hPQ hQR hPR
  have wi : i ≫ g = 0 := by
    apply comp_eq_zero_of_image_le_kernel
    rw [hker, factor_cokernelMap P R U hPR hRU hPU,
      imageSubobject_epi_comp]
  have heqSub : Subobject.mk i = Subobject.mk (kernel.ι g) := by
    change Subobject.mk i = kernelSubobject g
    rw [hker, factor_cokernelMap P R U hPR hRU hPU,
      imageSubobject_epi_comp, imageSubobject_mono]
  have hi : IsLimit (KernelFork.ofι i wi) := by
    apply (kernelIsKernel g).ofIsoLimit
    exact Fork.ext
      (Subobject.isoOfMkEqMk i (kernel.ι g) heqSub).symm
      (Subobject.ofMkLEMk_comp heqSub.ge)
  let j := Subobject.cokernelMapOfLE P Q R hPQ hQR hPR
  let fLift : X₁ ⟶ cokernel (Subobject.ofLE P R hPR) :=
    hi.lift (KernelFork.ofι f zero)
  have hjπ : j ≫ πMap = 0 := by
    simp only [j, πMap, Subobject.cokernelMapOfLE,
      Subobject.cokernelDescOfLE, Subobject.cokernelMap_ofLE,
      Subobject.cokernelDesc_ofLE]
    ext
    simp only [cokernel.π_desc_assoc, cokernel.π_desc, comp_zero,
      Category.assoc, cokernel.condition]
  have hfactor :
      Subobject.ofLE Q U hQU ≫ cokernel.π (Subobject.ofLE P U hPU) =
        cokernel.π (Subobject.ofLE P Q hPQ) ≫ j ≫ i := by
    rw [(Subobject.ofLE_comp_ofLE Q R U hQR hRU).symm,
      Category.assoc, factor_cokernelMap P R U hPR hRU hPU,
      ← Category.assoc (Subobject.ofLE Q R hQR),
      factor_cokernelMap P Q R hPQ hQR hPR, Category.assoc]
  have hfi : fLift ≫ i = f :=
    hi.fac (KernelFork.ofι f zero) WalkingParallelPair.zero
  have him : imageSubobject (fLift ≫ i) = imageSubobject (j ≫ i) := by
    rw [hfi, himg, hfactor, imageSubobject_epi_comp]
  have hjim : imageSubobject (j ≫ i) = Subobject.mk (j ≫ i) :=
    imageSubobject_mono _
  have hle : imageSubobject (fLift ≫ i) ≤ Subobject.mk (j ≫ i) := by
    rw [him, hjim]
  have hfactJI : (Subobject.mk (j ≫ i)).Factors (fLift ≫ i) := by
    apply Subobject.factors_of_le _ hle
    have h := imageSubobject_factors_comp_self
      (f := fLift ≫ i) (𝟙 _)
    simpa using h
  let φJI := (Subobject.mk (j ≫ i)).factorThru (fLift ≫ i) hfactJI
  have hφJI : φJI ≫ (Subobject.mk (j ≫ i)).arrow = fLift ≫ i :=
    Subobject.factorThru_arrow _ _ _
  have harrowJI : (Subobject.mk (j ≫ i)).arrow =
      (Subobject.underlyingIso (j ≫ i)).hom ≫ (j ≫ i) :=
    (Subobject.underlyingIso_hom_comp_eq_mk (j ≫ i)).symm
  let ψ := φJI ≫ (Subobject.underlyingIso (j ≫ i)).hom
  have hψj : ψ ≫ j = fLift := by
    apply (cancel_mono i).mp
    rw [Category.assoc]
    change (φJI ≫ (Subobject.underlyingIso (j ≫ i)).hom) ≫
      (j ≫ i) = fLift ≫ i
    rw [Category.assoc, ← harrowJI, hφJI]
  have wπ : fLift ≫ πMap = 0 := by
    rw [← hψj, Category.assoc, hjπ, comp_zero]
  have hπ : IsColimit (CokernelCofork.ofπ πMap wπ) := by
    have hφEq : φJI = factorThruImageSubobject (fLift ≫ i) ≫
        (Subobject.isoOfEq _ _ (him.trans hjim)).hom := by
      apply (cancel_mono (Subobject.mk (j ≫ i)).arrow).mp
      rw [hφJI, Category.assoc, Subobject.isoOfEq_hom,
        Subobject.ofLE_arrow, imageSubobject_arrow_comp]
    have hψEpi : Epi ψ := by
      change Epi (φJI ≫ (Subobject.underlyingIso (j ≫ i)).hom)
      rw [hφEq, Category.assoc]
      exact epi_comp _ _
    have hπFactor : cokernel.π j ≫
        (Subobject.thirdQuotientIso P Q R hPQ hQR hPR).hom = πMap :=
      cokernel.π_desc _ _ _
    let thirdIso := Subobject.thirdQuotientIso P Q R hPQ hQR hPR
    have hjs : ∀ (c : Cofork fLift 0), j ≫ Cofork.π c = 0 := by
      intro c
      haveI := hψEpi
      apply zero_of_epi_comp ψ
      rw [← Category.assoc, hψj]
      have hc := c.condition
      simp only [zero_comp] at hc
      exact hc
    exact Cofork.IsColimit.mk _
      (fun c => thirdIso.inv ≫ cokernel.desc j (Cofork.π c) (hjs c))
      (fun c => by
        change πMap ≫ thirdIso.inv ≫
          cokernel.desc j (Cofork.π c) (hjs c) = Cofork.π c
        rw [show πMap = cokernel.π j ≫ thirdIso.hom from hπFactor.symm,
          Category.assoc, thirdIso.hom_inv_id_assoc, cokernel.π_desc])
      (fun c m hm => by
        change cokernel (Subobject.ofLE Q R hQR) ⟶ c.pt at m
        change πMap ≫ m = Cofork.π c at hm
        change m = thirdIso.inv ≫ cokernel.desc j (Cofork.π c) (hjs c)
        rw [← cancel_epi thirdIso.hom, thirdIso.hom_inv_id_assoc]
        apply (cancel_epi (cokernel.π j)).mp
        rw [cokernel.π_desc, ← Category.assoc, hπFactor]
        exact hm)
  let h : (ShortComplex.mk f g zero).LeftHomologyData :=
    { K := cokernel (Subobject.ofLE P R hPR)
      H := cokernel (Subobject.ofLE Q R hQR)
      i := i
      π := πMap
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hπ }
  exact h.homologyIso

/-- The homology of the canonical finite page at one bidegree is the next
canonical quotient page. -/
noncomputable def pageHomologyIso (FC : FilteredComplex C)
    (n : ℕ) (p : ℤ × ℤ) :
    (FC.pageComplex n).homology p ≅
      FC.pageObj p.1 p.2 (↑(n + 1) : WithTop ℕ) := by
  rcases p with ⟨s, k⟩
  let K := FC.pageComplex n
  generalize ha : s - (n : ℤ) = a
  generalize hb : k + 1 = b
  let source : ℤ × ℤ := (a, b)
  let target : ℤ × ℤ := (s + (n : ℤ), k - 1)
  have hsource : (pageShape n).Rel source (s, k) := by
    change source + ((n : ℤ), (-1 : ℤ)) = (s, k)
    ext <;> simp only [source, Prod.fst_add, Prod.snd_add] <;> omega
  have hcenter : (a + (n : ℤ), b - 1) = (s, k) := by
    ext <;> omega
  have htarget : (pageShape n).Rel (s, k) target := by
    change (s, k) + ((n : ℤ), (-1 : ℤ)) = target
    simp [target, Int.sub_eq_add_neg]
  let S := K.sc' source (s, k) target
  let P := FC.boundarySubobject s k (↑n : WithTop ℕ)
  let Q := FC.boundarySubobject s k (↑(n + 1) : WithTop ℕ)
  let R := FC.cycleSubobject s k (↑(n + 1) : WithTop ℕ)
  let U := FC.cycleSubobject s k (↑n : WithTop ℕ)
  have hPQ : P ≤ Q :=
    FC.boundarySubobject_monotone s k (by exact_mod_cast Nat.le_succ n)
  have hQR : Q ≤ R := FC.B_le_Z_aux s k ↑(n + 1)
  have hRU : R ≤ U :=
    FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)
  have hPR : P ≤ R := hPQ.trans hQR
  have hPU : P ≤ U := hPR.trans hRU
  have hQU : Q ≤ U := hQR.trans hRU
  have hker : kernelSubobject S.g =
      imageSubobject (Subobject.ofLE R U hRU ≫
        cokernel.π (Subobject.ofLE P U (hPQ.trans (hQR.trans hRU)))) := by
    change kernelSubobject (FC.pageDifferentialHom n (s, k) target) = _
    rw [FC.pageDifferentialHom_of_rel n (s, k) target htarget]
    simp only [target, Int.sub_eq_add_neg, eqToHom_refl, Category.comp_id]
    change kernelSubobject (FC.pageDifferential s k n) =
      imageSubobject
        (Subobject.ofLE
            (FC.cycleSubobject s k ↑(n + 1))
            (FC.cycleSubobject s k ↑n)
            (FC.cycleSubobject_antitone s k
              (by exact_mod_cast Nat.le_succ n)) ≫
          FC.pageπ s k ↑n)
    apply le_antisymm
    · exact FC.pageDifferential_Z_succ_le s k n
    · exact FC.pageDifferential_Z_succ_ge s k n
  have himg : imageSubobject S.f =
      imageSubobject (Subobject.ofLE Q U (hQR.trans hRU) ≫
        cokernel.π (Subobject.ofLE P U (hPQ.trans (hQR.trans hRU)))) := by
    cases hcenter
    change imageSubobject
      (FC.pageDifferentialHom n source (a + (n : ℤ), b - 1)) = _
    rw [FC.pageDifferentialHom_of_rel n source
      (a + (n : ℤ), b - 1) hsource]
    simp only [source, eqToHom_refl, Category.comp_id]
    dsimp only [P, Q, R, U, pageπ]
    convert FC.pageDifferential_B_succ a b n using 1
    dsimp only [pageπ]
    congr
  let hS : S.homology ≅ FC.pageObj s k (↑(n + 1) : WithTop ℕ) :=
    nestedSubobjectHomologyIso P Q R U hPQ hQR hRU hPR hPU hQU
      S.f S.g S.zero hker himg
  exact K.homologyIsoSc' source (s, k) target
      ((pageShape n).prev_eq' hsource) ((pageShape n).next_eq' htarget) ≪≫ hS

/-- The canonical quotient pages of a filtered complex, assembled as a
Mathlib spectral sequence. -/
noncomputable def canonicalPageSpectralSequence (FC : FilteredComplex C) :
    CategoryTheory.SpectralSequence C (fun r : ℤ => pageShape r.toNat) 0 where
  page r hr := FC.pageComplex r.toNat
  iso r r' p hrr' hr := by
    subst r'
    exact FC.pageHomologyIso r.toNat p ≪≫ eqToIso (by
      change FC.pageObj p.1 p.2 (↑(r.toNat + 1) : WithTop ℕ) =
        FC.pageObj p.1 p.2 (↑((r + 1).toNat) : WithTop ℕ)
      congr 2
      omega)

end KIP126.Core.SpectralSequence.FilteredComplex
