import KIP126.Def.SpectralSequence.Basic.Category.Predicates

/-!
# Proofs about the spectral-sequence category
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A square commutes exactly when its maps commute at every underlying grading. -/
theorem SpectralSequence.commSq_iff_underlying
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {W X Y Z : SpectralSequence C ι}
    (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) :
    SpectralSequence.CommSq f g h i ↔
      ∀ (k : ι), f.φ k ≫ h.φ k = g.φ k ≫ i.φ k := by
  constructor
  · intro hsq k
    exact congrFun (congrArg SpectralSequenceMorphism.φ hsq.w) k
  · intro hsq
    constructor
    exact SpectralSequenceMorphism.ext (funext hsq)

end KIP126.Core.SpectralSequence
