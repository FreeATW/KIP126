import KIP126.Def.AdamsE2.Presentation.Data
import KIP126.External.Provenance

/-!
# Explicit external E₂ presentation evidence

No witness of this input is postulated globally. A caller supplies the actual
spectral sequence and its presentation evidence with provenance. The input
alone does not assert that an arbitrary Adams-shaped sequence is the sphere's
sequence, nor does it imply permanence of h₆².
-/

namespace KIP126.AdamsE2

open KIP126.Classical.Adams

/-- The single user-facing input for using the imported E₂ table. -/
structure Input where
  sequence : ClassicalAdamsSpectralSequence
  algebra : PageAlgebra sequence
  table : Table
  tableCorrect : KIP126.External.ExternalEvidence (Nonempty (Presentation table algebra))
  /-- These two checks inspect the imported numbers, not the unknown Ext page. -/
  h6_mem : (1, 64) ∈ table.region
  h6_dim : table.dim (1, 64) = 1

end KIP126.AdamsE2
