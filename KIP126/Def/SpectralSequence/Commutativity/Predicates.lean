import KIP126.Def.SpectralSequence.Commutativity.Square.Data
import KIP126.Def.SpectralSequence.Crossing.Predicates

/-!
# Crossing predicates for extension spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Historical ESS wrapper around `NoCrossing`. -/
def ESSNoCrossing {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {_conv₁ : Convergence E₁ A₁ F₁} {_conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism _conv₁ _conv₂}
    {_bnd₁ : F₁.IsBounded} {_bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS _conv₁ _conv₂ cm _bnd₁ _bnd₂)
    (dd : DifferentialDatum C ω) : Prop :=
  NoCrossing dd

/-- Historical ESS wrapper around `NoCrossingRange`. -/
def ESSNoCrossingRange {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {_conv₁ : Convergence E₁ A₁ F₁} {_conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism _conv₁ _conv₂}
    {_bnd₁ : F₁.IsBounded} {_bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS _conv₁ _conv₂ cm _bnd₁ _bnd₂)
    (dd : DifferentialDatum C ω) (p : ℤ) : Prop :=
  NoCrossingRange dd p

end KIP126.Core.SpectralSequence
