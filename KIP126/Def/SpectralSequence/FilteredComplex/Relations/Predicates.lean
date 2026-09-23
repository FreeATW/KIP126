import KIP126.Def.SpectralSequence.FilteredComplex.Relations.Data

/-! Predicates for filtered-complex/page relations. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace PageView

variable {FC : FilteredComplex C} (P : PageView FC)

/-- A filtered lift whose associated-graded image represents a page element. -/
def IsLift (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ)
    {T : C}
    (xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
    (x : P.element r hr s k T) : Prop :=
  ∃ z : T ⟶ Subobject.underlying.obj
      (FC.cycleSubobject s k (P.pageNumber r hr)),
    z ≫ (FC.cycleSubobject s k (P.pageNumber r hr)).arrow =
      xl ≫ FC.filtration.toAssociatedGraded s k ∧
    z ≫ FC.pageπ s k (P.pageNumber r hr) =
      x ≫ (P.pageToPage r hr s k).hom

/-- A page element relation induced by the page differential. -/
def relation (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ)
    {T : C} (x : P.element r hr s k T)
    (y : P.element r hr (s + r) (k - 1) T) : Prop :=
  MathlibModel.DifferentialRelation P.sequence r hr (s, k) (target r s k) x y

/-- The canonical page-level crossing predicate for a relation. -/
def crossed (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ)
    {T : C} (x : P.element r hr s k T)
    (y : P.element r hr (s + r) (k - 1) T)
    (h : P.relation r hr s k x y) : Prop :=
  MathlibModel.RelationCrossedBy (P.datum r hr s k) x y h

end PageView

end KIP126.Core.SpectralSequence.FilteredComplex
