import KIP126.Def.SpectralSequence.Convergence.Data

/-! Detection is a separately named relation on strong convergence data. -/
namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {FC : FilteredComplex C} {P : EndpointExtension FC}
variable {A : Type*} [Category A] [Abelian A]
variable {F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A}
variable [F.ShiftSequence ℤ] [F.IsHomological]

namespace StrongConvergenceWitness

/-- A limiting class detects a filtered generalized element when their images
agree in the associated graded piece selected by the bidegree.  Detection is
a relation: changing the filtered lift by the next filtration level does not
change the detected limiting class. -/
def Detects (W : StrongConvergenceWitness P A F)
    {T : A} {pq : ℤ × ℤ}
    (y : T ⟶ W.eInfinity pq)
    (x : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) : Prop :=
  y ≫ (W.eInfinityComparison pq).hom =
    x ≫ W.comparison.filtration.toAssociatedGraded
      (W.comparison.filtrationDegree pq) (pq.1 + pq.2)


end StrongConvergenceWitness

end KIP126.Core.SpectralSequence
