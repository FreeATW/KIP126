import KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Proofs
import KIP126.Def.SpectralSequence.FilteredComplex.WeakConvergence

/-!
# The bounded extension spectral sequence
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- The spectral sequence of the filtered two-term complex. -/
noncomputable def BoundedExtensionSS.ess
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  (ext.complex t).toSpectralSequence (ext.bounded t)

/-- Weak convergence of the extension spectral sequence to the historical
homology presentation of its two-term complex. -/
noncomputable def BoundedExtensionSS.weakConvergence
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    Convergence (ext.ess t)
      (ext.complex t).homologySSObj (ext.complex t).homologySSFiltration :=
  (ext.complex t).weakConvergence (ext.bounded t)

/-- The `E₀` object in chain degree `1`. -/
noncomputable def BoundedExtensionSS.e0PageAtOne
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (s : ℤ) : C :=
  (ext.complex t).assocGraded s 1

/-- The `E₀` object in chain degree `0`. -/
noncomputable def BoundedExtensionSS.e0PageAtZero
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (s : ℤ) : C :=
  (ext.complex t).assocGraded s 0

/-- The page-zero differential from chain degree `1` to chain degree `0`. -/
noncomputable def BoundedExtensionSS.d0
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (s : ℤ) :
    ext.e0PageAtOne t s ⟶ ext.e0PageAtZero t s :=
  (ext.complex t).assocGradedDiff s 1

end KIP126.Core.SpectralSequence
