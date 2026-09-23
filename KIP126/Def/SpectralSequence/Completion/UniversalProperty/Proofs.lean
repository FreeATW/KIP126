import KIP126.Def.SpectralSequence.Completion.UniversalProperty.Data

/-!
# Universal property of completion

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

set_option maxHeartbeats 8000000 in
lemma Filtration.completionLift_proj {ω : Type w} {A : ω → C}
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
  simp only [Filtration.completionProj', Filtration.completion,
    Filtration.completionFunctor]
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 32000000 in
lemma Filtration.completionLift_unique {ω : Type w} {A : ω → C}
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
    unfold Filtration.completionProj' Filtration.completion Filtration.completionFunctor
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

end KIP126.Core.SpectralSequence
