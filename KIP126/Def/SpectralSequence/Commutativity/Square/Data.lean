import KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Proofs
import KIP126.Def.SpectralSequence.Convergence.SSData.Category.Data

/-!
# Commutative squares of convergent spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A commutative square in the category of convergent spectral sequences. -/
structure ConvergingSSSquare {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w} where
  V₁ : ConvergingSS C ω ω'
  V₂ : ConvergingSS C ω ω'
  V₃ : ConvergingSS C ω ω'
  V₄ : ConvergingSS C ω ω'
  f : V₁ ⟶ V₂
  p : V₁ ⟶ V₃
  q : V₂ ⟶ V₄
  g : V₃ ⟶ V₄
  comm : f ≫ q = p ≫ g

/-- Historical componentwise presentation of a commutative square, including
bounded extension data on its four edges. -/
structure HomotopyCommSquare {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (conv₃ : Convergence E₃ A₃ F₃) (conv₄ : Convergence E₄ A₄ F₄) where
  cmf : ConvergenceMorphism conv₁ conv₂
  cmp : ConvergenceMorphism conv₁ conv₃
  cmq : ConvergenceMorphism conv₂ conv₄
  cmg : ConvergenceMorphism conv₃ conv₄
  bnd₁ : F₁.IsBounded
  bnd₂ : F₂.IsBounded
  bnd₃ : F₃.IsBounded
  bnd₄ : F₄.IsBounded
  extf : BoundedExtensionSS conv₁ conv₂ cmf bnd₁ bnd₂
  extp : BoundedExtensionSS conv₁ conv₃ cmp bnd₁ bnd₃
  extq : BoundedExtensionSS conv₂ conv₄ cmq bnd₂ bnd₄
  extg : BoundedExtensionSS conv₃ conv₄ cmg bnd₃ bnd₄
  abutment_comm : ∀ k', cmf.aMap k' ≫ cmq.aMap k' = cmp.aMap k' ≫ cmg.aMap k'
  eInfty_comm : ∀ k, cmf.eMap k ≫ cmq.eMap k = cmp.eMap k ≫ cmg.eMap k

/-- Convert the historical componentwise square to a categorical square. -/
def HomotopyCommSquare.toSquare {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄) :
    ConvergingSSSquare (C := C) (ω := ω) (ω' := ω') where
  V₁ := ⟨E₁, A₁, F₁, conv₁⟩
  V₂ := ⟨E₂, A₂, F₂, conv₂⟩
  V₃ := ⟨E₃, A₃, F₃, conv₃⟩
  V₄ := ⟨E₄, A₄, F₄, conv₄⟩
  f := sq.cmf
  p := sq.cmp
  q := sq.cmq
  g := sq.cmg
  comm := ConvergenceMorphism.ext
    (funext fun k => sq.eInfty_comm k)
    (funext fun k' => sq.abutment_comm k')

end KIP126.Core.SpectralSequence
