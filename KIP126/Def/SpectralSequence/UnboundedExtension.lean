import KIP126.Def.SpectralSequence.UnboundedExtension.TruncatedSpectralSequence.Data

/-!
# Unbounded extensions: verified truncation layer

This file migrates the axiom-free public core of
`KIPBase/SpectralSequence/UnboundedExtension.lean`: the truncated underlying
complex, its boundedness proof, and its spectral sequence.

The remaining source declarations are not re-exported here.  The transition
morphism contains unfinished cycle/boundary preservation proofs; page
stabilization and the limiting spectral sequence were placeholders; and weak
convergence was declared as a project `axiom`.  Those claims need actual
proofs, or explicitly supplied external evidence, before they can cross the
KIP126 trust boundary.
-/
