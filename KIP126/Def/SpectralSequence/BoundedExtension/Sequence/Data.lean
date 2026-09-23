import KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Predicates

/-!
# Bounded extension spectral-sequence input data
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- The two-term filtered complex underlying an extension at one stem. -/
noncomputable def BoundedExtensionSS.complex
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    FilteredComplex C :=
  underlyingComplex cm.aMap cm.filtration_compat t

end KIP126.Core.SpectralSequence
