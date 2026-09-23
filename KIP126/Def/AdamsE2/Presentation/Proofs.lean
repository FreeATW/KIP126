import KIP126.Def.AdamsE2.Presentation.Data

namespace KIP126.AdamsE2

open KIP126.Core.Algebra KIP126.Classical.Adams
open scoped BigOperators

noncomputable section

theorem Presentation.basis_mul {T : Table} {E : ClassicalAdamsSpectralSequence}
    {A : PageAlgebra E} (P : Presentation T A) (p q : Degree)
    (hp : p ∈ T.region) (hq : q ∈ T.region) (hpq : p + q ∈ T.region)
    (i : Fin (T.dim p)) (j : Fin (T.dim q)) :
    A.product p q (P.basis p hp i) (P.basis q hq j) =
      ∑ k, T.mulCoeff p q hp hq hpq i j k • P.basis (p + q) hpq k := by
  apply A.embed_injective (p + q)
  calc
    A.embed (p + q) (A.product p q (P.basis p hp i) (P.basis q hq j)) =
        A.embed p (P.basis p hp i) * A.embed q (P.basis q hq j) :=
      A.product_assembly p q _ _
    _ = P.comparison (T.generator p hp i * T.generator q hq j) := by
      rw [map_mul, P.generator_image, P.generator_image]
    _ = P.comparison (∑ k,
        T.mulCoeff p q hp hq hpq i j k • T.generator (p + q) hpq k) := by
      rw [T.generator_mul]
    _ = A.embed (p + q) (∑ k,
        T.mulCoeff p q hp hq hpq i j k • P.basis (p + q) hpq k) := by
      simp [P.generator_image]

theorem Presentation.basis_mul_eq_basis {T : Table} {E : ClassicalAdamsSpectralSequence}
    {A : PageAlgebra E} (P : Presentation T A) (p q : Degree)
    (hp : p ∈ T.region) (hq : q ∈ T.region) (hpq : p + q ∈ T.region)
    (i : Fin (T.dim p)) (j : Fin (T.dim q)) (k : Fin (T.dim (p + q)))
    (h : ∀ l, T.mulCoeff p q hp hq hpq i j l = if l = k then 1 else 0) :
    A.product p q (P.basis p hp i) (P.basis q hq j) = P.basis (p + q) hpq k := by
  rw [P.basis_mul p q hp hq hpq]
  simp [h]

theorem Presentation.basis_mul_eq_zero {T : Table} {E : ClassicalAdamsSpectralSequence}
    {A : PageAlgebra E} (P : Presentation T A) (p q : Degree)
    (hp : p ∈ T.region) (hq : q ∈ T.region) (hpq : p + q ∈ T.region)
    (i : Fin (T.dim p)) (j : Fin (T.dim q))
    (h : ∀ k, T.mulCoeff p q hp hq hpq i j k = 0) :
    A.product p q (P.basis p hp i) (P.basis q hq j) = 0 := by
  rw [P.basis_mul p q hp hq hpq]
  simp [h]

end
end KIP126.AdamsE2
