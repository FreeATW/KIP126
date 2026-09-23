import KIP126.Def.SpectralSequence.Commutativity.Detection.Data

/-!
# Compatibility of the detection projection
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The convergence isomorphisms intertwine the induced associated-graded
map with the transported infinity-page map. -/
theorem detectionGradedProj_compat
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₂ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₂ A₄ : ω' → C} {F₂ : Filtration A₂} {F₄ : Filtration A₄}
    {conv₂ : Convergence E₂ A₂ F₂} {conv₄ : Convergence E₄ A₄ F₄}
    (cmq : ConvergenceMorphism conv₂ conv₄) (k : ω) :
    (conv₂.iso k).hom ≫
        Filtration.inducedAssocGradedMap cmq.aMap cmq.filtration_compat
          (conv₂.reindex k).1 (conv₂.reindex k).2 =
      cmq.eMap k ≫ (conv₄.iso k).hom ≫ detectionGradedProj cmq k := by
  show (conv₂.iso k).hom ≫
        Filtration.inducedAssocGradedMap cmq.aMap cmq.filtration_compat
          (conv₂.reindex k).1 (conv₂.reindex k).2 =
      cmq.eMap k ≫ (conv₄.iso k).hom ≫
        F₄.transportGraded (congrFun cmq.reindex_eq k).symm
  exact (cmq.iso_compat k).symm

end KIP126.Core.SpectralSequence
