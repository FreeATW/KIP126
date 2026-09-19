import KIP126.Def.SpectralSequence.FilteredPage.Proofs

/-! Regression checks for the canonical filtered-complex quotient pages. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

example (FC : FilteredComplex C) (s k : ℤ) :
    Antitone (FC.cycleSubobject s k) :=
  FC.cycleSubobject_antitone s k

example (FC : FilteredComplex C) (s k : ℤ) :
    Monotone (FC.boundarySubobject s k) :=
  FC.boundarySubobject_monotone s k

example (FC : FilteredComplex C) (s k : ℤ) :
    FC.cycleSubobject s k 0 = ⊤ :=
  FC.cycleSubobject_zero s k

example (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ) :
    Subobject.underlying.obj (FC.cycleSubobject s k r) ⟶ FC.pageObj s k r :=
  FC.pageπ s k r

end

end KIP126.Core.SpectralSequence.FilteredComplex
