import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
import KIP126.Def.SpectralSequence.Convergence.SSData.Predicates

/-!
# Predicate selecting bounded extension input data
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- Marker for the bounded extension construction associated to a convergence morphism. -/
structure BoundedExtensionSS
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (cm : ConvergenceMorphism conv₁ conv₂)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) : Prop where

end KIP126.Core.SpectralSequence
