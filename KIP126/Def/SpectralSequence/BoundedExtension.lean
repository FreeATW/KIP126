import KIP126.Def.SpectralSequence.BoundedExtension.TwoTerm.Proofs
import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
import KIP126.Def.SpectralSequence.BoundedExtension.Sequence.Proofs
import KIP126.Def.SpectralSequence.BoundedExtension.SpectralSequence.Proofs
import KIP126.Def.SpectralSequence.BoundedExtension.Chain.Proofs
import KIP126.Def.SpectralSequence.BoundedExtension.Detection.Predicates
import KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Construction.Proofs
import KIP126.Def.SpectralSequence.BoundedExtension.BoundedComplex.Data
import KIP126.Def.SpectralSequence.BoundedExtension.SelfComplex.Data

/-!
# Bounded extension spectral sequences

This is the axiom-free migration of the usable declarations from
`KIPBase/SpectralSequence/BoundedExtension.lean`.  The historical names are
preserved in `KIP126.Core.SpectralSequence`, while the implementation reuses
KIP126's canonical filtered-complex machinery.

The old declarations `BoundedExtensionSS.essDiff` and
`BoundedExtensionSS.essBoundary` had unfinished object-valued bodies, so
they do not yet have a mathematical definition to migrate.  Consequently the
dependent `HasFExtension`, commutativity API, and the old functors whose map
proofs were also placeholders are deliberately outside this migration
frontier.  No replacement zero object or project-defined axiom is introduced.
-/
