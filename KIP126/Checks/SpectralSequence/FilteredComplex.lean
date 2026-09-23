import KIP126.Def.SpectralSequence.FilteredComplex.Data

/-!
# Regression checks for filtered-complex pages

These examples keep the canonical homology, cycle, and boundary declarations
reachable from the public filtered-complex API.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

example (FC : FilteredComplex C) (k : ℤ) :
    FC.homologyObj k = (FC.homologyShortComplex k).homology :=
  FC.homologyObj_apply k

example (FC : FilteredComplex C) :
    Nonempty (Algebra.Filtration FC.homologyObj) :=
  ⟨FC.homologyFiltration⟩

example (FC : FilteredComplex C) (k : ℤ) :
    FC.dToK k ≫ FC.complex.d k (k - 1) = 0 :=
  FC.dToK_comp_d k

example (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ) :
    FC.boundarySubobject s k r ≤ FC.cycleSubobject s k r :=
  FC.B_le_Z_aux s k r

end KIP126.Core.SpectralSequence
