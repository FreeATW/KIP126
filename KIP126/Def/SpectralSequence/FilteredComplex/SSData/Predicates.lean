import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Data
import KIP126.Def.Algebra.Filtration.Predicates

/-!
# Predicates for the historical filtered-complex API
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- Historical two-sided boundedness record, with its original field names. -/
structure IsBounded (FC : FilteredComplex C) where
  /-- Degreewise lower bound. -/
  lo : ℤ → ℤ
  /-- Degreewise upper bound. -/
  hi : ℤ → ℤ
  /-- The bounds occur in the expected order. -/
  lo_le_hi : ∀ k, lo k ≤ hi k
  /-- Low filtration levels are the whole object. -/
  boundedBelow : ∀ k s, s ≤ lo k → FC.fil s k = ⊤
  /-- High filtration levels are zero. -/
  boundedAbove : ∀ k s, hi k ≤ s → FC.fil s k = ⊥

/-- A filtered representative `xl` lifts the associated-graded element `x`. -/
def IsLift (FC : FilteredComplex C) {T : C} (s k : ℤ)
    (xl : T ⟶ Subobject.underlying.obj (FC.fil s k))
    (x : T ⟶ FC.assocGraded s k) : Prop :=
  xl ≫ FC.filToAssocGraded s k = x

end FilteredComplex

end KIP126.Core.SpectralSequence
