import KIP126.Def.SpectralSequence.Convergence.SSData.Proofs
import KIP126.Def.Algebra.Truncation.Data

/-!
# Truncation data for nested-subobject filtrations

The historical API is retained, while the quotient objects and transition
maps are delegated to KIP126's canonical algebra-filtration implementation.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The truncated object `A(k) / F^(s₀+1)(A(k))`. -/
@[reducible] noncomputable def Filtration.truncatedObj
    {ω : Type w} {A : ω → C} (fil : Filtration A) (s₀ : ℤ) (k : ω) : C :=
  fil.toAlgebra.quotientAt (s₀ + 1) k

/-- The quotient projection to the historical truncation level. -/
@[reducible] noncomputable def Filtration.truncationProj
    {ω : Type w} {A : ω → C} (fil : Filtration A) (s₀ : ℤ) (k : ω) :
    A k ⟶ fil.truncatedObj s₀ k :=
  fil.toAlgebra.quotientProjection (s₀ + 1) k

/-- The image filtration induced on a truncated object. -/
@[reducible] noncomputable def Filtration.truncatedFiltration
    {ω : Type w} {A : ω → C} (fil : Filtration A) (s₀ : ℤ) :
    Filtration (fil.truncatedObj s₀) :=
  (fil.toAlgebra.quotientFiltration (s₀ + 1)).toSpectralSequence

/-- Transition `A/F^(s₁+1) ⟶ A/F^(s₀+1)` for `s₀ ≤ s₁`. -/
noncomputable def Filtration.truncationTransition
    {ω : Type w} {A : ω → C} (fil : Filtration A)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (k : ω) :
    fil.truncatedObj s₁ k ⟶ fil.truncatedObj s₀ k :=
  fil.toAlgebra.quotientTransition (show s₀ + 1 ≤ s₁ + 1 by omega) k

/-- Map on truncated target objects induced by a convergence morphism. -/
noncomputable def ConvergenceMorphism.truncatedAMap
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (k' : ω') :
    F₁.truncatedObj s₀ k' ⟶ F₂.truncatedObj s₀ k' := by
  change cokernel ((F₁.F (s₀ + 1) k').arrow) ⟶
    cokernel ((F₂.F (s₀ + 1) k').arrow)
  exact cokernel.desc ((F₁.F (s₀ + 1) k').arrow)
    (cm.aMap k' ≫ cokernel.π ((F₂.F (s₀ + 1) k').arrow))
    (by
      obtain ⟨φ, hφ⟩ := cm.filtration_compat (s₀ + 1) k'
      rw [← Category.assoc, ← hφ, Category.assoc, cokernel.condition, comp_zero])

end KIP126.Core.SpectralSequence
