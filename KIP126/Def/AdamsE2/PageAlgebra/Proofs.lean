import KIP126.Def.AdamsE2.PageAlgebra.Data

namespace KIP126.AdamsE2.PageAlgebra

open KIP126.Core.Algebra KIP126.Classical.Adams
open scoped DirectSum

theorem embed_injective {E : ClassicalAdamsSpectralSequence}
    (A : PageAlgebra E) (p : Bidegree) : Function.Injective (A.embed p) := by
  intro x y h
  have h' := A.assembly.injective h
  have h'' := congrArg (fun z : ⨁ p : Bidegree, Page E p => z p) h'
  change (DFinsupp.single p x) p = (DFinsupp.single p y) p at h''
  simpa using h''

end KIP126.AdamsE2.PageAlgebra
