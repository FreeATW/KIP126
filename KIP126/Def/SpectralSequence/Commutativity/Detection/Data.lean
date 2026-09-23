import KIP126.Def.SpectralSequence.Convergence.SSData.Data

/-!
# Graded projection used in detection compatibility
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Transport an associated-graded target from the fourth convergence
reindexing to the second one. -/
noncomputable def detectionGradedProj
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₂ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₂ A₄ : ω' → C} {F₂ : Filtration A₂} {F₄ : Filtration A₄}
    {conv₂ : Convergence E₂ A₂ F₂} {conv₄ : Convergence E₄ A₄ F₄}
    (cmq : ConvergenceMorphism conv₂ conv₄) (k : ω) :
    F₄.associatedGraded (conv₄.reindex k).1 (conv₄.reindex k).2 ⟶
      F₄.associatedGraded (conv₂.reindex k).1 (conv₂.reindex k).2 :=
  eqToHom (by rw [cmq.reindex_eq])

end KIP126.Core.SpectralSequence
