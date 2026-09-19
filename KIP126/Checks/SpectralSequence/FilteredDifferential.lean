import KIP126.Def.SpectralSequence.FilteredDifferential.Proofs

/-! Regression checks for the canonical finite-page differential. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

example (FC : FilteredComplex C) (s k : ℤ) (n : ℕ) :
    FC.pageDifferential s k n ≫ FC.pageDifferential (s + ↑n) (k - 1) n = 0 :=
  FC.pageDifferential_comp s k n

end KIP126.Core.SpectralSequence.FilteredComplex
