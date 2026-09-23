import KIP126.Def.SpectralSequence.FilteredComplex.Data
import KIP126.Def.SpectralSequence.Basic.Data
import KIP126.Def.SpectralSequence.Convergence.SSData.Data

/-!
# Historical filtered-complex data API

This module exposes the data names used by `KIPBase.SpectralSequence.FilteredComplex`
on top of KIP126's canonical Mathlib `ChainComplex`-based implementation.  It does
not introduce a second filtered-complex structure: the old fields are compatibility
accessors for `complex` and `filtration`.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- Historical name for the underlying graded object. -/
@[reducible] def A (FC : FilteredComplex C) : ℤ → C :=
  FC.complex.X

/-- Historical one-index presentation of the chain differential. -/
noncomputable def d (FC : FilteredComplex C) (k : ℤ) :
    FC.A k ⟶ FC.A (k - 1) :=
  FC.complex.d k (k - 1)

/-- Historical name for the filtration subobjects. -/
@[reducible] def fil (FC : FilteredComplex C) (s k : ℤ) : Subobject (FC.A k) :=
  FC.filtration.F s k

/-- The chosen restriction of the differential to one filtration level. -/
noncomputable def filDiff (FC : FilteredComplex C) (s k : ℤ) :
    Subobject.underlying.obj (FC.fil s k) ⟶
      Subobject.underlying.obj (FC.fil s (k - 1)) :=
  (FC.differential_preserves s k).choose

/-- Historical name for an associated-graded piece. -/
@[reducible] noncomputable def assocGraded (FC : FilteredComplex C) (s k : ℤ) : C :=
  FC.filtration.associatedGraded s k

/-- Historical name for the quotient map onto an associated-graded piece. -/
@[reducible] noncomputable def filToAssocGraded (FC : FilteredComplex C) (s k : ℤ) :
    Subobject.underlying.obj (FC.fil s k) ⟶ FC.assocGraded s k :=
  FC.filtration.toAssociatedGraded s k

/-- Historical name for the differential induced on the associated graded. -/
@[reducible] noncomputable def assocGradedDiff (FC : FilteredComplex C) (s k : ℤ) :
    FC.assocGraded s k ⟶ FC.assocGraded s (k - 1) :=
  FC.associatedGradedDifferential s k

end FilteredComplex

end KIP126.Core.SpectralSequence
