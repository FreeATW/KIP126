import KIP126.Def.SpectralSequence.Truncation.Predicates
import KIP126.Def.Algebra.Truncation.Proofs

/-!
# Proofs for nested-subobject filtration truncations
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

omit [Abelian C] in
/-- Extend the one-step descending-filtration map to arbitrary comparable indices. -/
lemma Filtration.mono_of_le {ω : Type w} {A : ω → C}
    (fil : Filtration A) {s₁ s₂ : ℤ} (h : s₁ ≤ s₂) (k : ω) :
    fil.F s₂ k ≤ fil.F s₁ k := by
  have key : ∀ n : ℕ, fil.F (s₁ + ↑n) k ≤ fil.F s₁ k := by
    intro n
    induction n with
    | zero =>
        simp only [Nat.cast_zero, add_zero]
        exact le_rfl
    | succ n ih =>
        have step : fil.F (s₁ + ↑(n + 1)) k ≤ fil.F (s₁ + ↑n) k := by
          have : s₁ + ↑(n + 1) = (s₁ + ↑n) + 1 := by
            push_cast
            ring
          rw [this]
          exact fil.mono _ k
        exact le_trans step ih
  have h2 : s₂ = s₁ + ↑(s₂ - s₁).toNat := by omega
  rw [h2]
  exact key _

/-- Convert historical bounded-below data to the canonical predicate. -/
def Filtration.IsBoundedBelow.toAlgebra
    {ω : Type w} {A : ω → C} {fil : Filtration A}
    (hbb : fil.IsBoundedBelow) : fil.toAlgebra.IsBoundedBelow where
  lower := hbb.lo
  eq_top_of_le := hbb.boundedBelow

/-- The truncated filtration is bounded when the original is bounded below. -/
noncomputable def Filtration.truncatedFiltration_isBounded
    {ω : Type w} {A : ω → C} {fil : Filtration A}
    (hbb : fil.IsBoundedBelow) (s₀ : ℤ) :
    (fil.truncatedFiltration s₀).IsBounded := by
  let hb := fil.toAlgebra.quotientFiltration_isBounded hbb.toAlgebra (s₀ + 1)
  exact
    { lo := hb.lower
      hi := hb.upper
      lo_le_hi := hb.lower_le_upper
      boundedBelow := hb.eq_top_of_le
      boundedAbove := hb.eq_bot_of_le }

/-- Transition maps compose. -/
theorem Filtration.truncationTransition_comp
    {ω : Type w} {A : ω → C} (fil : Filtration A)
    {s₀ s₁ s₂ : ℤ} (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ ≤ s₂) (k : ω) :
    fil.truncationTransition h₁₂ k ≫ fil.truncationTransition h₀₁ k =
      fil.truncationTransition (le_trans h₀₁ h₁₂) k := by
  simpa only [Filtration.truncationTransition] using
    fil.toAlgebra.quotientTransition_comp
      (show s₀ + 1 ≤ s₁ + 1 by omega)
      (show s₁ + 1 ≤ s₂ + 1 by omega) k

/-- Quotient projections commute with transition maps. -/
theorem Filtration.truncationProj_transition
    {ω : Type w} {A : ω → C} (fil : Filtration A)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (k : ω) :
    fil.truncationProj s₁ k ≫ fil.truncationTransition h k =
      fil.truncationProj s₀ k := by
  exact fil.toAlgebra.quotientProjection_transition
    (show s₀ + 1 ≤ s₁ + 1 by omega) k

/-- The original target map commutes with the two truncation projections. -/
theorem ConvergenceMorphism.truncationProj_truncatedAMap
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (k' : ω') :
    F₁.truncationProj s₀ k' ≫ cm.truncatedAMap s₀ k' =
      cm.aMap k' ≫ F₂.truncationProj s₀ k' := by
  change cokernel.π ((F₁.F (s₀ + 1) k').arrow) ≫
      cokernel.desc ((F₁.F (s₀ + 1) k').arrow)
        (cm.aMap k' ≫ cokernel.π ((F₂.F (s₀ + 1) k').arrow)) _ =
    cm.aMap k' ≫ cokernel.π ((F₂.F (s₀ + 1) k').arrow)
  exact cokernel.π_desc _ _ _

/-- The truncated target map preserves the induced truncated filtrations. -/
theorem ConvergenceMorphism.truncatedFiltrationCompat
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ s : ℤ) (k' : ω') :
    ∃ φ : Subobject.underlying.obj ((F₁.truncatedFiltration s₀).F s k') ⟶
        Subobject.underlying.obj ((F₂.truncatedFiltration s₀).F s k'),
      φ ≫ ((F₂.truncatedFiltration s₀).F s k').arrow =
        ((F₁.truncatedFiltration s₀).F s k').arrow ≫ cm.truncatedAMap s₀ k' := by
  obtain ⟨φ_s, hφ_s⟩ := cm.filtration_compat s k'
  have sq_comm : φ_s ≫ ((F₂.F s k').arrow ≫ F₂.truncationProj s₀ k') =
      ((F₁.F s k').arrow ≫ F₁.truncationProj s₀ k') ≫
        cm.truncatedAMap s₀ k' := by
    rw [Category.assoc, cm.truncationProj_truncatedAMap s₀ k']
    rw [← Category.assoc (F₁.F s k').arrow, ← hφ_s, Category.assoc]
  let sq : Arrow.mk ((F₁.F s k').arrow ≫ F₁.truncationProj s₀ k') ⟶
      Arrow.mk ((F₂.F s k').arrow ≫ F₂.truncationProj s₀ k') :=
    Arrow.homMk φ_s (cm.truncatedAMap s₀ k') sq_comm
  exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩

end KIP126.Core.SpectralSequence
