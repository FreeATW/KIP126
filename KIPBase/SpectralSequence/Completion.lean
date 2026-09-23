/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Completion of filtered objects and Mittag-Leffler condition.
Reference: informal/completion.md
-/

import KIPBase.SpectralSequence.Truncation

universe u v w

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

/-! ### Monotonicity helper -/

omit [Abelian C] [HasLimitsOfShape ℕᵒᵖ C] in
lemma Filtration.mono_of_le {ω : Type w} {A : ω → C}
    (fil : Filtration A) {s₁ s₂ : ℤ} (h : s₁ ≤ s₂) (k : ω) :
    fil.F s₂ k ≤ fil.F s₁ k := by
  have key : ∀ n : ℕ, fil.F (s₁ + ↑n) k ≤ fil.F s₁ k := by
    intro n; induction n with
    | zero => simp only [Nat.cast_zero, add_zero]; exact le_rfl
    | succ n ih =>
      have step : fil.F (s₁ + ↑(n + 1)) k ≤ fil.F (s₁ + ↑n) k := by
        have : s₁ + ↑(n + 1) = (s₁ + ↑n) + 1 := by push_cast; ring
        rw [this]; exact fil.mono _ k
      exact le_trans step ih
  have h2 : s₂ = s₁ + ↑(s₂ - s₁).toNat := by omega
  rw [h2]; exact key _

/-! ### Completion of filtered objects

The completion of `A(k)` with respect to filtration `F` is the inverse limit
of the quotients `A(k)/F^{s+1}(A(k))` as `s → -∞`. -/

/-- The truncation system as a functor `ℕᵒᵖ ⥤ C`: sends `n` to
    `A(k)/F^{lo(k)+n+1}(A(k))` with transition maps from `truncationTransition`. -/
noncomputable def Filtration.completionFunctor {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) :
    ℕᵒᵖ ⥤ C where
  obj n := fil.truncatedObj (hbb.lo k + ↑n.unop) k
  map {m n} f := fil.truncationTransition (by have := leOfHom f.unop; omega) k
  map_id n := by
    apply (cancel_epi (cokernel.π ((fil.F (hbb.lo k + ↑n.unop + 1) k).arrow))).mp
    erw [Category.comp_id]; exact cokernel.π_desc _ _ _
  map_comp {l m n} f g := (fil.truncationTransition_comp _ _ k).symm

-- Abelian categories lack countable limits in general; this instance is the
-- sole structural sorry for the completion construction.
noncomputable instance Filtration.hasLimitCompletionFunctor {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) :
    HasLimit (fil.completionFunctor hbb k) := inferInstance

/-- The completion of `A(k)`: the inverse limit of its truncations. -/
noncomputable def Filtration.completion {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) : C :=
  limit (fil.completionFunctor hbb k)

/-- Projection from the completion to `truncatedObj s k` for arbitrary `s`. -/
noncomputable def Filtration.completionProj' {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s : ℤ) :
    fil.completion hbb k ⟶ fil.truncatedObj s k :=
  limit.π (fil.completionFunctor hbb k) (Opposite.op (s - hbb.lo k).toNat) ≫
    fil.truncationTransition (show s ≤ hbb.lo k + ↑(s - hbb.lo k).toNat by omega) k

private lemma Filtration.completionProj'_factor {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s : ℤ) :
    fil.completionProj' hbb k (s + 1) ≫ fil.truncationTransition (show s ≤ s + 1 by omega) k =
    fil.completionProj' hbb k s := by
  simp only [Filtration.completionProj']
  rw [Category.assoc, fil.truncationTransition_comp]
  have hw := limit.w (fil.completionFunctor hbb k)
    (homOfLE (show (s - hbb.lo k).toNat ≤ (s + 1 - hbb.lo k).toNat by omega)).op
  erw [← hw, Category.assoc, fil.truncationTransition_comp]
    <;> first | omega | (simp; omega)

/-- The canonical map `A(k) → Â(k)` to the completion. -/
noncomputable def Filtration.toCompletion {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) :
    A k ⟶ fil.completion hbb k :=
  limit.lift (fil.completionFunctor hbb k) {
    pt := A k
    π := {
      app := fun n => by exact fil.truncationProj (hbb.lo k + ↑n.unop) k
      naturality := by
        intro m n f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact (fil.truncationProj_transition
          (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑m.unop from
            by have := leOfHom f.unop; omega) k).symm
    }
  }

/-- The induced filtration on the completion: `F^s(Â(k)) = ker(Â(k) → A/F^{s+1})`. -/
noncomputable def Filtration.completionFiltration {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) :
    Filtration (fil.completion hbb) where
  F s k := kernelSubobject (fil.completionProj' hbb k s)
  mono s k := by
    rw [← fil.completionProj'_factor hbb k s]
    exact kernelSubobject_comp_le _ _

private lemma imageSubobject_ofLE_eq_bot_of_eq_bot {B : C} (X Y : Subobject B) (h : X ≤ Y)
    (hX : X = ⊥) : imageSubobject (Subobject.ofLE X Y h) = ⊥ := by
  subst hX
  have : Subobject.ofLE ⊥ Y h = 0 := by
    rw [← cancel_mono Y.arrow, Subobject.ofLE_arrow, Subobject.bot_arrow, zero_comp]
  rw [this, imageSubobject_zero]

/-! ### Mittag-Leffler condition

A filtration satisfies the Mittag-Leffler condition if for each `k` and `s`,
the images of `F^{s+n} ↪ F^s` stabilize as `n → ∞`. -/

/-- The Mittag-Leffler condition: images of deeper filtration levels in a
    given level stabilize. -/
def Filtration.IsMittagLeffler {ω : Type w} {A : ω → C}
    (fil : Filtration A) : Prop :=
  ∀ (k : ω) (s : ℤ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
    imageSubobject (Subobject.ofLE (fil.F (s + ↑n) k) (fil.F s k)
      (fil.mono_of_le (by omega) k)) =
    imageSubobject (Subobject.ofLE (fil.F (s + ↑N) k) (fil.F s k)
      (fil.mono_of_le (by omega) k))

/-- Bounded-above filtrations satisfy Mittag-Leffler. -/
theorem Filtration.IsBoundedAbove.toIsMittagLeffler {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hba : fil.IsBoundedAbove) : fil.IsMittagLeffler := by
  intro k s
  use (hba.hi k - s).toNat
  intro n hn
  have hN : hba.hi k ≤ s + ↑((hba.hi k - s).toNat) := by omega
  have hn' : hba.hi k ≤ s + ↑n := by omega
  rw [imageSubobject_ofLE_eq_bot_of_eq_bot _ _ _ (hba.boundedAbove k _ hn'),
      imageSubobject_ofLE_eq_bot_of_eq_bot _ _ _ (hba.boundedAbove k _ hN)]

/-- Bounded filtrations satisfy Mittag-Leffler. -/
theorem Filtration.IsBounded.toIsMittagLeffler {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBounded) : fil.IsMittagLeffler :=
  hb.toIsBoundedAbove.toIsMittagLeffler

/-! ### Properties of completion -/

private lemma Filtration.completionProj'_general {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) :
    fil.completionProj' hbb k s₁ ≫ fil.truncationTransition h k =
    fil.completionProj' hbb k s₀ := by
  simp only [Filtration.completionProj']
  rw [Category.assoc, fil.truncationTransition_comp]
  have hw := limit.w (fil.completionFunctor hbb k)
    (homOfLE (show (s₀ - hbb.lo k).toNat ≤ (s₁ - hbb.lo k).toNat by omega)).op
  erw [← hw, Category.assoc, fil.truncationTransition_comp]
    <;> first | omega | (simp; omega)

private noncomputable def Filtration.completionψ {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s₀ : ℤ) :
    (fil.completionFiltration hbb).truncatedObj s₀ k ⟶ fil.truncatedObj (s₀ + 1) k :=
  cokernel.desc
    ((kernelSubobject (fil.completionProj' hbb k (s₀ + 1))).arrow)
    (fil.completionProj' hbb k (s₀ + 1))
    (kernelSubobject_arrow_comp _)

private lemma Filtration.completionψ_factorization {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s₀ : ℤ) :
    (fil.completionFiltration hbb).truncationProj s₀ k ≫ fil.completionψ hbb k s₀ =
    fil.completionProj' hbb k (s₀ + 1) :=
  cokernel.π_desc _ _ _

private noncomputable instance Filtration.completionψ_mono {ω : Type w} {A : ω → C}
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

private lemma Filtration.completionψ_naturality {ω : Type w} {A : ω → C}
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

private noncomputable def Filtration.completionConeLeg {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k) (n : ℕᵒᵖ) :
    T ⟶ fil.truncatedObj (hbb.lo k + ↑n.unop) k := by
  let s := hbb.lo k + ↑n.unop
  have step1 : T ⟶ (fil.completionFiltration hbb).truncatedObj s k := f s
  have step2 : (fil.completionFiltration hbb).truncatedObj s k ⟶ fil.truncatedObj (s + 1) k :=
    fil.completionψ hbb k s
  have step3 : fil.truncatedObj (s + 1) k ⟶ fil.truncatedObj s k :=
    fil.truncationTransition (show s ≤ s + 1 by omega) k
  exact step1 ≫ step2 ≫ step3

private lemma Filtration.completionConeLeg_naturality {ω : Type w} {A : ω → C}
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

private noncomputable def Filtration.completionLift {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k)
    (hcompat : ∀ (s₀ s₁ : ℤ) (h : s₀ ≤ s₁),
      f s₁ ≫ (fil.completionFiltration hbb).truncationTransition h k = f s₀) :
    T ⟶ fil.completion hbb k :=
  limit.lift (fil.completionFunctor hbb k) {
    pt := T
    π := {
      app := fun n => fil.completionConeLeg hbb k T f n
      naturality := by
        intro m n φ
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact fil.completionConeLeg_naturality hbb k T f hcompat m n φ
    }
  }

private lemma Filtration.completionLift_proj {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k)
    (hcompat : ∀ (s₀ s₁ : ℤ) (h : s₀ ≤ s₁),
      f s₁ ≫ (fil.completionFiltration hbb).truncationTransition h k = f s₀)
    (s₀ : ℤ) :
    fil.completionLift hbb k T f hcompat ≫
      (fil.completionFiltration hbb).truncationProj s₀ k = f s₀ := by
  -- Cancel mono ψ(s₀) on the right
  apply (cancel_mono (fil.completionψ hbb k s₀)).mp
  rw [Category.assoc, fil.completionψ_factorization hbb k s₀]
  -- Goal: completionLift ≫ completionProj'(s₀+1) = f(s₀) ≫ ψ(s₀)
  -- Unfold completionProj'
  simp only [Filtration.completionProj']
  -- Goal: completionLift ≫ limit.π(op N) ≫ tr(s₀+1 ≤ lo+N) = f(s₀) ≫ ψ(s₀)
  -- where N = (s₀+1-lo).toNat
  rw [← Category.assoc]
  -- Goal: (completionLift ≫ limit.π(op N)) ≫ tr(...) = f(s₀) ≫ ψ(s₀)
  -- Use limit.lift_π to evaluate completionLift ≫ limit.π
  simp only [Filtration.completionLift]
  erw [limit.lift_π]
  -- Goal: completionConeLeg(op N) ≫ tr(...) = f(s₀) ≫ ψ(s₀)
  -- Unfold completionConeLeg
  unfold Filtration.completionConeLeg
  -- Goal: (f(lo+N) ≫ ψ(lo+N) ≫ tr(lo+N ≤ lo+N+1)) ≫ tr(s₀+1 ≤ lo+N) = f(s₀) ≫ ψ(s₀)
  rw [Category.assoc, Category.assoc]
  -- Goal: f(lo+N) ≫ ψ(lo+N) ≫ tr(lo+N ≤ lo+N+1) ≫ tr(s₀+1 ≤ lo+N) = f(s₀) ≫ ψ(s₀)
  -- Compose transitions: tr(lo+N ≤ lo+N+1) ≫ tr(s₀+1 ≤ lo+N) = tr(s₀+1 ≤ lo+N+1)
  rw [fil.truncationTransition_comp
    (show s₀ + 1 ≤ hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat by omega)
    (show hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat ≤
      hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat + 1 by omega)]
  -- Goal: f(lo+N) ≫ ψ(lo+N) ≫ tr(s₀+1 ≤ lo+N+1) = f(s₀) ≫ ψ(s₀)
  -- Use ψ_naturality: ψ(lo+N) ≫ tr(s₀+1 ≤ lo+N+1) = cFil.trTr(s₀ ≤ lo+N) ≫ ψ(s₀)
  rw [← fil.completionψ_naturality hbb k
    (show s₀ ≤ hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat by omega)]
  -- Goal: f(lo+N) ≫ cFil.trTr(s₀ ≤ lo+N) ≫ ψ(s₀) = f(s₀) ≫ ψ(s₀)
  -- Use hcompat: f(lo+N) ≫ cFil.trTr(s₀ ≤ lo+N) = f(s₀)
  rw [← Category.assoc, hcompat _ _
    (show s₀ ≤ hbb.lo k + ↑(s₀ + 1 - hbb.lo k).toNat by omega)]

private lemma Filtration.completionLift_unique {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k)
    (hcompat : ∀ (s₀ s₁ : ℤ) (h : s₀ ≤ s₁),
      f s₁ ≫ (fil.completionFiltration hbb).truncationTransition h k = f s₀)
    (g' : T ⟶ fil.completion hbb k)
    (hg' : ∀ s₀ : ℤ, g' ≫ (fil.completionFiltration hbb).truncationProj s₀ k = f s₀) :
    g' = fil.completionLift hbb k T f hcompat := by
  apply limit.hom_ext
  intro ⟨n⟩
  simp only [Filtration.completionLift]
  erw [limit.lift_π]
  unfold Filtration.completionConeLeg
  -- Goal: g' ≫ limit.π(op n) = f(lo+n) ≫ ψ(lo+n) ≫ tr(lo+n ≤ lo+n+1)
  -- Step 1: completionProj'(lo+↑n) = limit.π(op n) via limit.w
  have h_proj_eq_π : fil.completionProj' hbb k (hbb.lo k + ↑n) =
      limit.π (fil.completionFunctor hbb k) (Opposite.op n) := by
    unfold Filtration.completionProj'
    have hlef : n ≤ (hbb.lo k + ↑n - hbb.lo k).toNat := by omega
    have hw := limit.w (fil.completionFunctor hbb k) (homOfLE hlef).op
    -- hw : limit.π(op N₀) ≫ completionFunctor.map _ = limit.π(op n)
    -- Goal: limit.π(op N₀) ≫ truncationTransition _ k = limit.π(op n)
    -- completionFunctor.map = truncationTransition by definition
    exact hw
  -- Step 2: completionProj'(lo+↑n) = completionProj'(lo+↑n+1) ≫ tr(lo+↑n ≤ lo+↑n+1)
  -- by completionProj'_factor
  -- Step 3: completionProj'(lo+↑n+1) = cFil.truncationProj(lo+↑n) ≫ ψ(lo+↑n)
  -- by ψ_factorization
  -- Step 4: hg'(lo+↑n): g' ≫ cFil.truncationProj(lo+↑n) = f(lo+↑n)
  -- Combine: g' ≫ limit.π(op n) = g' ≫ completionProj'(lo+↑n)
  --        = g' ≫ completionProj'(lo+↑n+1) ≫ tr(lo+↑n ≤ lo+↑n+1)
  --        = g' ≫ (cFil.truncationProj(lo+↑n) ≫ ψ(lo+↑n)) ≫ tr(lo+↑n ≤ lo+↑n+1)
  --        = f(lo+↑n) ≫ ψ(lo+↑n) ≫ tr(lo+↑n ≤ lo+↑n+1)
  rw [← h_proj_eq_π, ← fil.completionProj'_factor hbb k (hbb.lo k + ↑n),
    ← Category.assoc, ← fil.completionψ_factorization hbb k (hbb.lo k + ↑n),
    ← Category.assoc, hg' (hbb.lo k + ↑n), Category.assoc]

/-- The completion is complete with respect to its own filtration. -/
theorem Filtration.completion_isComplete {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) :
    (fil.completionFiltration hbb).IsComplete := by
  intro k T f hcompat
  exact ⟨fil.completionLift hbb k T f (fun s₀ s₁ h => hcompat h),
    fil.completionLift_proj hbb k T f (fun s₀ s₁ h => hcompat h),
    fun g' hg' => fil.completionLift_unique hbb k T f (fun s₀ s₁ h => hcompat h) g' hg'⟩

end KIPBase.SpectralSequence
