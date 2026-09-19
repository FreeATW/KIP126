import KIP126.Def.SpectralSequence.FilteredComplex.Data

/-!
# Quotient pages of a filtered complex

The cycle and boundary subobjects determine these objects directly. This
module adds no alternative spectral-sequence structure.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The quotient of page cycles by page boundaries, including the infinity page. -/
noncomputable def pageObj (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ) : C :=
  cokernel (Subobject.ofLE (FC.boundarySubobject s k r)
    (FC.cycleSubobject s k r) (FC.B_le_Z_aux s k r))

/-- Projection from the cycle subobject to its quotient page. -/
noncomputable def pageπ (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ) :
    Subobject.underlying.obj (FC.cycleSubobject s k r) ⟶ FC.pageObj s k r :=
  cokernel.π (Subobject.ofLE (FC.boundarySubobject s k r)
    (FC.cycleSubobject s k r) (FC.B_le_Z_aux s k r))

end KIP126.Core.SpectralSequence.FilteredComplex
