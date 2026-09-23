import KIP126.Def.SpectralSequence.Basic.Category.Data

/-!
# Categorical predicates for nested-subobject spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A commutative square in the category of nested-subobject spectral sequences. -/
abbrev SpectralSequence.CommSq
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {W X Y Z : SpectralSequence C ι}
    (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop :=
  CategoryTheory.CommSq f g h i

end KIP126.Core.SpectralSequence
