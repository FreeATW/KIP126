import Mathlib.Algebra.Homology.SpectralSequence.Basic

namespace KIP126.Core.SpectralSequence

structure PageLevelConvention where
  firstPage : ℕ
  admissibleFrom : ℤ
  page : ℕ → ℤ
  cycleLevel : ℕ → ℤ
  quotientExponent : ℕ → ℤ
  page_first : page firstPage = admissibleFrom
  page_succ : ∀ r, page (r + 1) = page r + 1
  cycle_succ : ∀ r, cycleLevel (r + 1) = cycleLevel r + 1
  quotient_succ : ∀ r, quotientExponent (r + 1) = quotientExponent r + 1
  cycleLevel_eq_quotientExponent : ∀ r,
    cycleLevel r = quotientExponent r

end KIP126.Core.SpectralSequence
