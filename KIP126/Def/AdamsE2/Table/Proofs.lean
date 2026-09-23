import KIP126.Def.AdamsE2.Table.Data

namespace KIP126.AdamsE2.Table

open KIP126.Core.Algebra
open scoped BigOperators

noncomputable section

theorem generator_mul (T : Table) (p q : Degree)
    (hp : p ∈ T.region) (hq : q ∈ T.region) (hpq : p + q ∈ T.region)
    (i : Fin (T.dim p)) (j : Fin (T.dim q)) :
    T.generator p hp i * T.generator q hq j =
      ∑ k, T.mulCoeff p q hp hq hpq i j k • T.generator (p + q) hpq k := by
  have h : T.quotient (T.mulRelation p q hp hq hpq i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inr ⟨p, q, hp, hq, hpq, i, j, rfl⟩))
  simpa [mulRelation, generator, map_sub, map_mul, map_sum, sub_eq_zero] using h

theorem generator_unit (T : Table) :
    (∑ i, T.unitCoeff i • T.generator (0, 0) T.zero_mem i) = 1 := by
  have h : T.quotient T.unitRelation = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl rfl))
  simpa [unitRelation, generator, map_sub, map_sum, sub_eq_zero] using h

/-- A coordinate lookup can certify a product without unfolding the model ring. -/
theorem generator_mul_eq_generator (T : Table) (p q : Degree)
    (hp : p ∈ T.region) (hq : q ∈ T.region) (hpq : p + q ∈ T.region)
    (i : Fin (T.dim p)) (j : Fin (T.dim q)) (k : Fin (T.dim (p + q)))
    (h : ∀ l, T.mulCoeff p q hp hq hpq i j l = if l = k then 1 else 0) :
    T.generator p hp i * T.generator q hq j = T.generator (p + q) hpq k := by
  rw [T.generator_mul p q hp hq hpq]
  simp [h]

theorem generator_mul_eq_zero (T : Table) (p q : Degree)
    (hp : p ∈ T.region) (hq : q ∈ T.region) (hpq : p + q ∈ T.region)
    (i : Fin (T.dim p)) (j : Fin (T.dim q))
    (h : ∀ k, T.mulCoeff p q hp hq hpq i j k = 0) :
    T.generator p hp i * T.generator q hq j = 0 := by
  rw [T.generator_mul p q hp hq hpq]
  simp [h]

theorem generator_mem_piece (T : Table) (p : Degree) (hp : p ∈ T.region)
    (i : Fin (T.dim p)) : T.generator p hp i ∈ T.piece p := by
  refine ⟨T.symbol p hp i, ?_, rfl⟩
  change MvPolynomial.IsWeightedHomogeneous (fun g : T.Generator => g.1.val)
    (MvPolynomial.X (⟨⟨p, hp⟩, i⟩ : T.Generator) : T.Poly) p
  exact MvPolynomial.isWeightedHomogeneous_X F2
    (fun g : T.Generator => g.1.val) ⟨⟨p, hp⟩, i⟩

end
end KIP126.AdamsE2.Table
