import KIP126.Def.SpectralSequence.PageLevel.Data

namespace KIP126.Core.SpectralSequence

namespace PageLevelConvention

theorem page_ge (P : PageLevelConvention) {r : ℕ}
    (h : P.firstPage ≤ r) : P.admissibleFrom ≤ P.page r := by
  induction r, h using Nat.le_induction with
  | base => simp [P.page_first]
  | succ r _ ih => rw [P.page_succ]; omega

theorem cycleLevel_ge (P : PageLevelConvention) {r : ℕ}
    (h : P.firstPage ≤ r) :
    P.cycleLevel P.firstPage ≤ P.cycleLevel r := by
  induction r, h using Nat.le_induction with
  | base => rfl
  | succ r _ ih => rw [P.cycle_succ]; omega

theorem quotientExponent_ge (P : PageLevelConvention) {r : ℕ}
    (h : P.firstPage ≤ r) :
    P.quotientExponent P.firstPage ≤ P.quotientExponent r := by
  induction r, h using Nat.le_induction with
  | base => rfl
  | succ r _ ih => rw [P.quotient_succ]; omega

end PageLevelConvention

end KIP126.Core.SpectralSequence
