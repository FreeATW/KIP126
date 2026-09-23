import KIP126.Def.SpectralSequence.Commutativity.Basic.Proofs
import KIP126.Def.SpectralSequence.Commutativity.Predicates
import KIP126.Def.SpectralSequence.Commutativity.Square.Proofs
import KIP126.Def.SpectralSequence.Commutativity.Detection.Proofs

/-!
# Commutativity for extension spectral-sequence data

This entry point contains the axiom-free part of
`KIPBase/SpectralSequence/Commutativity.lean`: both square presentations,
their conversion, the induced associated-graded commutative square, and the
detection-index transport.

The source's `ESSRelation` and `ESSVanishes` referred to `essDiff`, whose
object-valued definition was itself unfinished.  The claimed differential,
boundary-transfer, page-functoriality, and detection theorems were likewise
unfinished.  They are intentionally not restated as facts here.  They can be
added after a concrete ESS differential object is defined and the proofs are
completed.
-/
