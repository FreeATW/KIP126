import KIP126.Def.AdamsE2.Table.Proofs
import KIP126.Def.AdamsE2.PageAlgebra.Proofs

/-!
# A table presents the actual E₂ page

`Nonempty (Presentation T A)` is the external mathematical assertion. Its
algebra homomorphism maps into the *actual* page algebra of the supplied
spectral sequence. Degreewise equivalences are required only on the covered
region; the basis fields bind the imported dimensions and generator IDs to
this same homomorphism.
-/

namespace KIP126.AdamsE2

open KIP126.Core.Algebra KIP126.Classical.Adams

structure Presentation (T : Table) {E : ClassicalAdamsSpectralSequence}
    (A : PageAlgebra E) where
  comparison : T.Model →ₐ[F2] A.Total
  onDegree : ∀ p, T.piece p →ₗ[F2] Page E p
  compatible : ∀ p (x : T.piece p),
    comparison x.val = A.embed p (onDegree p x)
  bijective : ∀ p, p ∈ T.region → Function.Bijective (onDegree p)
  basis : ∀ p, p ∈ T.region → Module.Basis (Fin (T.dim p)) F2 (Page E p)
  generator_image : ∀ p (hp : p ∈ T.region) i,
    comparison (T.generator p hp i) = A.embed p (basis p hp i)

end KIP126.AdamsE2
