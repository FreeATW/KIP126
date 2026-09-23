import KIP126.Def.SpectralSequence.Truncation.Data

/-!
# Completeness predicate for nested-subobject filtrations
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtration is complete when its canonical maps to all truncations have
the expected universal property. -/
def Filtration.IsComplete {ω : Type w} {A : ω → C}
    (fil : Filtration A) : Prop :=
  ∀ (k : ω) (T : C) (f : ∀ s₀ : ℤ, T ⟶ fil.truncatedObj s₀ k),
    (∀ {s₀ s₁ : ℤ} (h : s₀ ≤ s₁),
      f s₁ ≫ fil.truncationTransition h k = f s₀) →
    ∃! (g : T ⟶ A k), ∀ s₀ : ℤ, g ≫ fil.truncationProj s₀ k = f s₀

end KIP126.Core.SpectralSequence
