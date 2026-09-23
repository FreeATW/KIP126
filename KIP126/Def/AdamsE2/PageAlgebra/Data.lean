import KIP126.Def.ClassicalAdams.Page.Data
import Mathlib.Algebra.DirectSum.Module

/-!
# Multiplication on the E₂ page of an existing spectral sequence

The underlying pages are the existing Mathlib objects. A linear equivalence
identifies their direct sum with a commutative F₂-algebra, and the product is
required to preserve bidegrees. No sphere, resolution or new page carrier is
constructed here.
-/

namespace KIP126.AdamsE2

open KIP126.Core.Algebra KIP126.Classical.Adams
open scoped DirectSum

abbrev Page (E : ClassicalAdamsSpectralSequence) (p : Bidegree) : Type :=
  (E.page 2 (by decide)).X p

structure PageAlgebra (E : ClassicalAdamsSpectralSequence) where
  Total : Type
  [commRing : CommRing Total]
  [algebra : Algebra F2 Total]
  assembly : (⨁ p : Bidegree, Page E p) ≃ₗ[F2] Total
  product : ∀ p q, Page E p →ₗ[F2] Page E q →ₗ[F2] Page E (p + q)
  product_assembly : ∀ p q (x : Page E p) (y : Page E q),
    assembly (DirectSum.lof F2 Bidegree (Page E) (p + q) (product p q x y)) =
      assembly (DirectSum.lof F2 Bidegree (Page E) p x) *
        assembly (DirectSum.lof F2 Bidegree (Page E) q y)
  unit : Page E (0, 0)
  unit_assembly : assembly (DirectSum.lof F2 Bidegree (Page E) (0, 0) unit) = 1

attribute [instance] PageAlgebra.commRing PageAlgebra.algebra

noncomputable def PageAlgebra.embed {E : ClassicalAdamsSpectralSequence}
    (A : PageAlgebra E) (p : Bidegree) : Page E p →ₗ[F2] A.Total :=
  A.assembly.toLinearMap.comp (DirectSum.lof F2 Bidegree (Page E) p)

end KIP126.AdamsE2
