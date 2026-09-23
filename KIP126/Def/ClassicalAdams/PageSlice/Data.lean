import KIP126.Def.ClassicalAdams.SphereSequence.Data

/-!
# Classical spectral-sequence basics

The concrete Adams sequence is the Mathlib spectral-sequence object exposed by
`KIP126.Classical.Adams.ClassicalAdamsSS`; this module records its page slice.
-/

namespace KIP126.Classical.SpectralSequence

open KIP126.Classical.Adams

abbrev AdamsE₂E₃Slice {stable : StableHomotopyContext}
    {X : stable.Spectrum} (A : ClassicalAdamsSS stable X) :=
  (A.E₂, A.E₃)

end KIP126.Classical.SpectralSequence
