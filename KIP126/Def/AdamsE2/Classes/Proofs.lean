import KIP126.Def.AdamsE2.Classes.Data
import KIP126.Def.AdamsE2.Presentation.Proofs

namespace KIP126.AdamsE2.Input

theorem h6_ne_zero (myAdams : Input) : myAdams.h6 ≠ 0 :=
  (myAdams.presentation.basis (1, 64) myAdams.h6_mem).ne_zero _

end KIP126.AdamsE2.Input
