import KIP126.External.AdamsE2

namespace KIP126.AdamsE2.Input

noncomputable def presentation (myAdams : Input) :
    Presentation myAdams.table myAdams.algebra :=
  Classical.choice myAdams.tableCorrect.evidence

noncomputable def h6 (myAdams : Input) : Page myAdams.sequence (1, 64) :=
  myAdams.presentation.basis (1, 64) myAdams.h6_mem
    ⟨0, by rw [myAdams.h6_dim]; decide⟩

/-- The square is the actual E₂ product, not an independently imported class. -/
noncomputable def h6Square (myAdams : Input) : Page myAdams.sequence (2, 128) :=
  myAdams.algebra.product (1, 64) (1, 64) myAdams.h6 myAdams.h6

end KIP126.AdamsE2.Input
