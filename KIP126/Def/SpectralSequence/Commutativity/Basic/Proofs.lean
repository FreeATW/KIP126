import KIP126.Def.SpectralSequence.BoundedExtension.SpectralSequence.Data

/-!
# Definitional facts about extension spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The ambient object of the extension spectral sequence is the associated
graded object of its two-term filtered complex. -/
theorem ess_ssData_V {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (s k : ℤ) :
    (((ext.complex t).toSpectralSequence (ext.bounded t)).ssData ⟨s, k⟩).V =
      (ext.complex t).assocGraded s k :=
  rfl

/-- The extension spectral sequence has differential degree `(r, -1)`. -/
theorem ess_diffDeg {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (r : ℤ) :
    ((ext.complex t).toSpectralSequence (ext.bounded t)).diffDeg r = (r, -1) :=
  rfl

end KIP126.Core.SpectralSequence
