import KIP126.Def.SpectralSequence.Commutativity.Square.Data
import KIP126.Def.SpectralSequence.Convergence.SSData.Proofs

/-!
# Compatibility properties of commutative convergence squares
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The categorical commutativity proof in `toSquare` is exactly the one
assembled from the two historical component equations. -/
theorem HomotopyCommSquare.toSquare_comm
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄) :
    sq.toSquare.comm = ConvergenceMorphism.ext
      (funext fun k => sq.eInfty_comm k)
      (funext fun k' => sq.abutment_comm k') :=
  rfl

/-- The square commutes on infinity-page maps. -/
theorem essCommutativity_eInfty_compat
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (_n : ℤ) (k : ω) :
    sq.cmf.eMap k ≫ sq.cmq.eMap k = sq.cmp.eMap k ≫ sq.cmg.eMap k :=
  sq.eInfty_comm k

/-- The associated-graded maps induced by the four sides form a commutative
square. -/
theorem essCommutativity_filtration_compat
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (s : ℤ) (k' : ω') :
    Filtration.inducedAssocGradedMap sq.cmf.aMap sq.cmf.filtration_compat s k' ≫
        Filtration.inducedAssocGradedMap sq.cmq.aMap sq.cmq.filtration_compat s k' =
      Filtration.inducedAssocGradedMap sq.cmp.aMap sq.cmp.filtration_compat s k' ≫
        Filtration.inducedAssocGradedMap sq.cmg.aMap sq.cmg.filtration_compat s k' := by
  have hL := Filtration.inducedAssocGradedMap_comp sq.cmf sq.cmq s k'
  have hR := Filtration.inducedAssocGradedMap_comp sq.cmp sq.cmg s k'
  have hcomp : (fun k'' => sq.cmf.aMap k'' ≫ sq.cmq.aMap k'') =
      fun k'' => sq.cmp.aMap k'' ≫ sq.cmg.aMap k'' :=
    funext fun k'' => sq.abutment_comm k''
  have hmain : Filtration.inducedAssocGradedMap
      (fun k'' => sq.cmf.aMap k'' ≫ sq.cmq.aMap k'')
      (ConvergenceMorphismData.fcComp sq.cmf sq.cmq) s k' =
    Filtration.inducedAssocGradedMap
      (fun k'' => sq.cmp.aMap k'' ≫ sq.cmg.aMap k'')
      (ConvergenceMorphismData.fcComp sq.cmp sq.cmg) s k' := by
    rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap]
    rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap]
    apply Filtration.inducedGradedMapOfMap_congr
    funext s₀ k₀
    apply (cancel_mono ((F₄.F s₀ k₀).arrow)).mp
    rw [(ConvergenceMorphismData.fcComp sq.cmf sq.cmq s₀ k₀).choose_spec,
      (ConvergenceMorphismData.fcComp sq.cmp sq.cmg s₀ k₀).choose_spec,
      congrFun hcomp k₀]
  rw [← hL, ← hR, hmain]

end KIP126.Core.SpectralSequence
