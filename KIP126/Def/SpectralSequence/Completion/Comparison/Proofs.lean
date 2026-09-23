import KIP126.Def.SpectralSequence.Completion.Comparison.Data

/-!
# Comparison proofs for the completed filtration

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]


lemma Filtration.completionProj'_general {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) :
    fil.completionProj' hbb k s₁ ≫ fil.truncationTransition h k =
    fil.completionProj' hbb k s₀ := by
  simp only [Filtration.completionProj', Filtration.completion,
    Filtration.completionFunctor]
  rw [Category.assoc, fil.truncationTransition_comp]
  have hw := limit.w (fil.completionFunctor hbb k)
    (homOfLE (show (s₀ - hbb.lo k).toNat ≤ (s₁ - hbb.lo k).toNat by omega)).op
  erw [← hw, Category.assoc, fil.truncationTransition_comp]
  all_goals simp only [Opposite.unop_op]
  · rfl
  · omega


lemma Filtration.completionψ_factorization {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s₀ : ℤ) :
    (fil.completionFiltration hbb).truncationProj s₀ k ≫ fil.completionψ hbb k s₀ =
    fil.completionProj' hbb k (s₀ + 1) :=
  cokernel.π_desc _ _ _

noncomputable instance Filtration.completionψ_mono {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s₀ : ℤ) :
    Mono (fil.completionψ hbb k s₀) := by
  have harr := (kernelSubobject_arrow (fil.completionProj' hbb k (s₀ + 1))).symm
  have key : fil.completionψ hbb k s₀ =
    (cokernelIsoOfEq harr).hom ≫
    (cokernelEpiComp (kernelSubobjectIso (fil.completionProj' hbb k (s₀ + 1))).hom
      (kernel.ι (fil.completionProj' hbb k (s₀ + 1)))).hom ≫
    (Abelian.coimageIsoImage' (fil.completionProj' hbb k (s₀ + 1))).hom ≫
    image.ι (fil.completionProj' hbb k (s₀ + 1)) := by
    apply (cancel_epi (cokernel.π
      ((kernelSubobject (fil.completionProj' hbb k (s₀ + 1))).arrow))).mp
    rw [Filtration.completionψ, cokernel.π_desc,
      π_comp_cokernelIsoOfEq_hom_assoc, cokernelEpiComp_hom, cokernel.π_desc_assoc,
      Abelian.coimageIsoImage'_hom, cokernel.π_desc_assoc, image.fac]
  rw [key]
  have : IsIso ((cokernelIsoOfEq harr).hom ≫
    (cokernelEpiComp (kernelSubobjectIso (fil.completionProj' hbb k (s₀ + 1))).hom
      (kernel.ι (fil.completionProj' hbb k (s₀ + 1)))).hom ≫
    (Abelian.coimageIsoImage' (fil.completionProj' hbb k (s₀ + 1))).hom) := by
    apply IsIso.comp_isIso
  exact mono_comp _ _

lemma Filtration.completionψ_naturality {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) :
    (fil.completionFiltration hbb).truncationTransition h k ≫ fil.completionψ hbb k s₀ =
    fil.completionψ hbb k s₁ ≫ fil.truncationTransition (show s₀ + 1 ≤ s₁ + 1 by omega) k := by
  haveI : Epi ((fil.completionFiltration hbb).truncationProj s₁ k) := by
    show Epi (cokernel.π _); infer_instance
  apply (cancel_epi ((fil.completionFiltration hbb).truncationProj s₁ k)).mp
  rw [← Category.assoc,
    (fil.completionFiltration hbb).truncationProj_transition h k,
    fil.completionψ_factorization,
    ← Category.assoc, fil.completionψ_factorization,
    fil.completionProj'_general hbb k (show s₀ + 1 ≤ s₁ + 1 by omega)]

set_option maxHeartbeats 8000000 in
lemma Filtration.completionConeLeg_naturality {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k)
    (hcompat : ∀ (s₀ s₁ : ℤ) (h : s₀ ≤ s₁),
      f s₁ ≫ (fil.completionFiltration hbb).truncationTransition h k = f s₀)
    (m n : ℕᵒᵖ) (φ : m ⟶ n) :
    fil.completionConeLeg hbb k T f n =
    fil.completionConeLeg hbb k T f m ≫ (fil.completionFunctor hbb k).map φ := by
  have hle : n.unop ≤ m.unop := leOfHom φ.unop
  unfold Filtration.completionConeLeg
  dsimp only [Filtration.completionFunctor]
  -- After unfolding, goal is:
  -- f(lo+n) ≫ ψ(lo+n) ≫ tr₁ = (f(lo+m) ≫ ψ(lo+m) ≫ tr₂) ≫ tr₃
  -- where tr₁ : lo+n ≤ lo+n+1, tr₂ : lo+m ≤ lo+m+1, tr₃ : lo+n ≤ lo+m
  -- First, flatten the RHS
  rw [Category.assoc, Category.assoc]
  -- RHS = f(lo+m) ≫ ψ(lo+m) ≫ tr₂ ≫ tr₃
  -- Collapse tr₂ ≫ tr₃ to single transition
  conv_rhs => rw [fil.truncationTransition_comp
    (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑m.unop by omega)
    (show hbb.lo k + ↑m.unop ≤ hbb.lo k + ↑m.unop + 1 by omega)]
  -- RHS = f(lo+m) ≫ ψ(lo+m) ≫ tr(lo+n ≤ lo+m+1)
  -- Split this transition: tr(lo+n ≤ lo+m+1) = tr(lo+n+1 ≤ lo+m+1) ≫ tr(lo+n ≤ lo+n+1)
  conv_rhs => rw [← fil.truncationTransition_comp
    (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑n.unop + 1 by omega)
    (show hbb.lo k + ↑n.unop + 1 ≤ hbb.lo k + ↑m.unop + 1 by omega)]
  -- RHS = f(lo+m) ≫ ψ(lo+m) ≫ tr(lo+n+1 ≤ lo+m+1) ≫ tr(lo+n ≤ lo+n+1)
  -- Use ψ_naturality: ψ(lo+m) ≫ tr(lo+n+1 ≤ lo+m+1) = cFil.trTr(lo+n ≤ lo+m) ≫ ψ(lo+n)
  rw [← Category.assoc (fil.completionψ hbb k _)]
  rw [← fil.completionψ_naturality hbb k
    (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑m.unop by omega)]
  -- RHS is: f(lo+m) ≫ cFil.trTr(lo+n ≤ lo+m) ≫ ψ(lo+n) ≫ tr(lo+n ≤ lo+n+1)
  -- Use hcompat: f(lo+m) ≫ cFil.trTr(lo+n ≤ lo+m) = f(lo+n)
  have hc := hcompat _ _ (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑m.unop by omega)
  -- Rewrite RHS: f(lo+m) ≫ trTr ≫ ψ ≫ tr  →  f(lo+n) ≫ ψ ≫ tr
  slice_rhs 1 2 => rw [hc]
  simp only [Category.assoc]

end KIP126.Core.SpectralSequence
