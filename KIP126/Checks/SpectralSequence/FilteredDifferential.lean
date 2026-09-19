import KIP126.Def.SpectralSequence.FilteredDifferential.Proofs

/-! Regression checks for the canonical finite-page differential. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

example (FC : FilteredComplex C) (s k : ℤ) (n : ℕ) :
    FC.pageDifferential s k n ≫ FC.pageDifferential (s + ↑n) (k - 1) n = 0 :=
  FC.pageDifferential_comp s k n

example (FC : FilteredComplex C) (s k : ℤ) (n : ℕ) :
    imageSubobject (
        Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
          (FC.cycleSubobject s k ↑n)
          (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
        FC.pageπ s k ↑n) ≤
      kernelSubobject (FC.pageDifferential s k n) :=
  FC.pageDifferential_Z_succ_ge s k n

example (FC : FilteredComplex C) (s k : ℤ) (n : ℕ) :
    kernelSubobject (FC.pageDifferential s k n) ≤
      imageSubobject (
        Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
          (FC.cycleSubobject s k ↑n)
          (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
        FC.pageπ s k ↑n) :=
  FC.pageDifferential_Z_succ_le s k n

example (FC : FilteredComplex C) (s k : ℤ) (n : ℕ) :
    imageSubobject (FC.pageDifferential s k n) =
      imageSubobject (
        Subobject.ofLE (FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1))
          (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)
          (le_trans (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑(n + 1))
            (FC.cycleSubobject_antitone (s + ↑n) (k - 1)
              (by exact_mod_cast Nat.le_succ n))) ≫
        FC.pageπ (s + ↑n) (k - 1) ↑n) :=
  FC.pageDifferential_B_succ s k n

end KIP126.Core.SpectralSequence.FilteredComplex
