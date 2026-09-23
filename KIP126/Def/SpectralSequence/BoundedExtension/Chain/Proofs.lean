import KIP126.Def.SpectralSequence.BoundedExtension.Chain.Data
import KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Proofs

/-!
# Bounded extensions in a composable chain
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

set_option linter.defProp false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- The extension spectral sequence for the first morphism in a
three-spectra chain. -/
noncomputable def ThreeSpectraChain.boundedEssF
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (chain : ThreeSpectraChain conv₁ conv₂ conv₃) :
    BoundedExtensionSS conv₁ conv₂ chain.cm₁₂ chain.bnd₁ chain.bnd₂ :=
  BoundedExtensionSS.mk' conv₁ conv₂ chain.cm₁₂ chain.bnd₁ chain.bnd₂

/-- The extension spectral sequence for the second morphism in a
three-spectra chain. -/
noncomputable def ThreeSpectraChain.boundedEssG
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (chain : ThreeSpectraChain conv₁ conv₂ conv₃) :
    BoundedExtensionSS conv₂ conv₃ chain.cm₂₃ chain.bnd₂ chain.bnd₃ :=
  BoundedExtensionSS.mk' conv₂ conv₃ chain.cm₂₃ chain.bnd₂ chain.bnd₃

end KIP126.Core.SpectralSequence
