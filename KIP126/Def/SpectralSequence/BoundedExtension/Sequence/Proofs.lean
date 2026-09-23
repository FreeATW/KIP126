import KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Data
import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs

/-!
# Boundedness proof for extension spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- The standard bounded extension marker. -/
theorem BoundedExtensionSS.mk'
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (cm : ConvergenceMorphism conv₁ conv₂)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) :
    BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂ := ⟨⟩

/-- The underlying two-term filtered complex is bounded. -/
noncomputable def BoundedExtensionSS.bounded
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    (ext.complex t).IsBounded :=
  underlyingComplexBounded cm.aMap cm.filtration_compat t bnd₁ bnd₂

end KIP126.Core.SpectralSequence
