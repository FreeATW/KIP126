import KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Predicates

/-!
# Composable convergence morphisms

Data for the pair of bounded extension spectral sequences attached to a
composable pair of convergence morphisms.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- A composable pair of convergence morphisms `V₁ ⟶ V₂ ⟶ V₃`, together
with boundedness of all three target filtrations. -/
structure ThreeSpectraChain
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    (conv₁ : Convergence E₁ A₁ F₁)
    (conv₂ : Convergence E₂ A₂ F₂)
    (conv₃ : Convergence E₃ A₃ F₃) where
  /-- The first convergence morphism. -/
  cm₁₂ : ConvergenceMorphism conv₁ conv₂
  /-- The second convergence morphism. -/
  cm₂₃ : ConvergenceMorphism conv₂ conv₃
  /-- Boundedness of the first target filtration. -/
  bnd₁ : F₁.IsBounded
  /-- Boundedness of the second target filtration. -/
  bnd₂ : F₂.IsBounded
  /-- Boundedness of the third target filtration. -/
  bnd₃ : F₃.IsBounded

end KIP126.Core.SpectralSequence
