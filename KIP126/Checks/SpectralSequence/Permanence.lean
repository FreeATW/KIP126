import KIP126.Def.SpectralSequence.Permanence.Data

/-! Type-level regressions for the elementwise permanence interface. -/

namespace KIP126.Checks.SpectralSequence.Permanence

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

universe w

variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ r : ℤ}
variable (E : CategoryTheory.SpectralSequence F2ModuleCat c r₀)
variable (hr : r₀ ≤ r) (p : κ) (x : (E.page r hr).X p)

example (h : IsPermanent E r hr p x) : x ≠ 0 := h.ne_zero

example (trajectory : PageTrajectory E r hr p x) :
    trajectory.classAt 0 = x := trajectory.classAt_zero

end KIP126.Checks.SpectralSequence.Permanence
