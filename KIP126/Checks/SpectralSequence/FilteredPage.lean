import KIP126.Def.SpectralSequence.FilteredPage.AssemblyProofs

/-! Regression checks for the canonical filtered-complex quotient pages. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C}

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

example (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ) :
    FC.boundarySubobject s k ⊥ ≤ FC.cycleSubobject s k r :=
  FC.boundarySubobject_bot_le_cycle s k r

example (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ)
    (h : FC.boundarySubobject s k r = FC.cycleSubobject s k r) :
    IsZero (FC.pageObj s k r) :=
  FC.pageObj_isZero_of_eq s k r h

example (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ) :
    IsZero (FC.pageObj s k r) ↔
      FC.boundarySubobject s k r = FC.cycleSubobject s k r :=
  FC.pageObj_isZero_iff s k r

example (FC : FilteredComplex C) (s k : ℤ) (r : WithTop ℕ)
    (h : IsZero (FC.pageObj s k r)) :
    FC.boundarySubobject s k r = FC.cycleSubobject s k r :=
  FC.eq_of_pageObj_isZero s k r h

example (FC : FilteredComplex C) (n : ℕ) :
    HomologicalComplex C (pageShape n) :=
  FC.pageComplex n

example (FC : FilteredComplex C) (n : ℕ) (p : ℤ × ℤ) :
    (FC.pageComplex n).homology p ≅
      FC.pageObj p.1 p.2 (↑(n + 1) : WithTop ℕ) :=
  FC.pageHomologyIso n p

example (FC : FilteredComplex C) :
    CategoryTheory.SpectralSequence C (fun r : ℤ => pageShape r.toNat) 0 :=
  FC.canonicalPageSpectralSequence

example (FC : FilteredComplex C) (n : ℕ) (p q : ℤ × ℤ)
    (_hpq : (pageShape n).Rel p q) :
    (FC.pageComplex n).d p q = FC.pageDifferentialHom n p q := rfl

example (P Q R : Subobject (C := C) X) (hPQ : P ≤ Q) (hQR : Q ≤ R) :
    cokernel (Subobject.cokernelMapOfLE P Q R hPQ hQR) ≅
      cokernel (Subobject.ofLE Q R hQR) :=
  Subobject.thirdQuotientIso P Q R hPQ hQR

end

end KIP126.Core.SpectralSequence.FilteredComplex
