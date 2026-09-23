import KIP126.Def.SpectralSequence.Completion.Proofs

/-!
# The filtration on a completion

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

noncomputable def Filtration.completionFiltration {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) :
    Filtration (fil.completion hbb) where
  F s k := kernelSubobject (fil.completionProj' hbb k s)
  mono s k := by
    rw [← fil.completionProj'_factor hbb k s]
    exact kernelSubobject_comp_le _ _

end KIP126.Core.SpectralSequence
