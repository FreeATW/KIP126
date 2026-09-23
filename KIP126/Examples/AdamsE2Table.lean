import KIP126.Def.AdamsE2
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# 用三个格点演示模型环与真实 E₂ 的分层

这个最小例子只导入三个一维格点，形式基元为 `1`, `x`, `y`，
并导入关系 `x * x = y`。因为 `x * y` 的目标次数不在覆盖域中，
数据不声称 `x * y = 0`。

`ModelRing` 是由这些生成元和覆盖范围内的乘法关系定义的模型环。
我们先完全在模型环中检查关系和非零性。只有给定 `Presentation`
这个带来源的外部表示定理后，`pageH6` 才是已有谱序列的真实
`E₂` 元素。这里没有用表重新定义 `E₂`，也没有伪造外部见证。
-/

namespace KIP126.Examples.AdamsE2Table

open KIP126.AdamsE2 KIP126.Core.Algebra KIP126.Classical.Adams
open scoped BigOperators

/-- Replace this definition by a generated table when real data is available. -/
def table : Table where
  region := {(0, 0), (1, 64), (2, 128)}
  dim := fun _ => 1
  mulCoeff := fun _ _ _ _ _ _ _ _ => 1
  zero_mem := by simp
  unitCoeff := fun _ => 1

theorem h6_covered : (1, 64) ∈ table.region := by simp [table]
theorem square_covered : (2, 128) ∈ table.region := by simp [table]
theorem cube_not_covered : (3, 192) ∉ table.region := by simp [table]

private theorem filtration_nonneg (p : Degree) (hp : p ∈ table.region) : 0 ≤ p.1 := by
  simp only [table, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

noncomputable section

/-- 数据首先定义这个模型环，而不是定义真实 `E₂` 页。 -/
abbrev ModelRing := table.Model

def modelX : ModelRing := table.generator (1, 64) h6_covered (0 : Fin 1)
def modelY : ModelRing := table.generator (2, 128) square_covered (0 : Fin 1)

/-- The relation comes from the input table, with no computation of Ext. -/
theorem x_mul_x : modelX * modelX = modelY := by
  have h := table.generator_mul (1, 64) (1, 64)
    h6_covered h6_covered square_covered (0 : Fin 1) (0 : Fin 1)
  change modelX * modelX =
    ∑ k : Fin 1, (1 : F2) • table.generator (2, 128) square_covered k at h
  rw [Fintype.sum_unique, one_smul] at h
  have hi : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simpa only [hi, modelY] using h

def polynomialEvaluation : table.Poly →ₐ[F2] Polynomial F2 :=
  MvPolynomial.aeval (fun g => Polynomial.X ^ g.1.val.1.toNat)

private theorem evaluate_symbol (p : Degree) (hp : p ∈ table.region)
    (i : Fin (table.dim p)) :
    polynomialEvaluation (table.symbol p hp i) = Polynomial.X ^ p.1.toNat := by
  exact MvPolynomial.aeval_X (fun g : table.Generator => Polynomial.X ^ g.1.val.1.toNat)
    (⟨⟨p, hp⟩, i⟩ : table.Generator)

theorem relations_vanish :
    table.relationIdeal ≤ RingHom.ker polynomialEvaluation.toRingHom := by
  apply Ideal.span_le.mpr
  rintro f (rfl | ⟨p, q, hp, hq, hpq, i, j, rfl⟩)
  · change polynomialEvaluation
      ((∑ i : Fin 1, (1 : F2) • table.symbol (0, 0) table.zero_mem i) - 1) = 0
    simp only [map_sub, map_sum, map_one, evaluate_symbol,
      one_smul, Int.toNat_zero, pow_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, sub_self]
  · change polynomialEvaluation
      (table.symbol p hp i * table.symbol q hq j -
        ∑ k : Fin 1, (1 : F2) • table.symbol (p + q) hpq k) = 0
    simp only [map_sub, map_mul, map_sum, evaluate_symbol,
      one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    change Polynomial.X ^ p.1.toNat * Polynomial.X ^ q.1.toNat -
      Polynomial.X ^ (p.1 + q.1).toNat = (0 : Polynomial F2)
    rw [Int.toNat_add (filtration_nonneg p hp) (filtration_nonneg q hq), pow_add, sub_self]

/-- This map checks the model without assuming any Adams computation. -/
def modelEvaluation : table.Model →ₐ[F2] Polynomial F2 :=
  Ideal.Quotient.liftₐ table.relationIdeal polynomialEvaluation
    (fun _ h => relations_vanish h)

theorem evaluate_generator (p : Degree) (hp : p ∈ table.region)
    (i : Fin (table.dim p)) :
    modelEvaluation (table.generator p hp i) = Polynomial.X ^ p.1.toNat := by
  simp [modelEvaluation, Table.generator, Table.quotient,
    Ideal.Quotient.liftₐ_apply, polynomialEvaluation, Table.symbol]

theorem y_ne_zero : modelY ≠ 0 := by
  intro h
  have hh := congrArg modelEvaluation h
  simp [modelY, evaluate_generator] at hh

/-- The missing product stays nonzero in this model, rather than being
silently zero-filled at the edge of the table. -/
theorem x_mul_y_ne_zero : modelX * modelY ≠ 0 := by
  intro h
  have hh := congrArg modelEvaluation h
  simp [modelX, modelY, map_mul, evaluate_generator] at hh

variable (E : ClassicalAdamsSpectralSequence) (A : PageAlgebra E)

def modelH6Class : table.piece (1, 64) :=
  ⟨modelX, table.generator_mem_piece (1, 64) h6_covered (0 : Fin 1)⟩

def modelH6SqClass : table.piece (2, 128) :=
  ⟨modelY, table.generator_mem_piece (2, 128) square_covered (0 : Fin 1)⟩

/-- `h₆` 是模型生成元在真实 `E₂` 页上的像。 -/
def pageH6 (P : Presentation table A) : Page E (1, 64) :=
  P.onDegree (1, 64) modelH6Class

/-- 模型中标记为 `h₆²` 的基元在真实 `E₂` 页上的像。 -/
def pageH6Sq (P : Presentation table A) : Page E (2, 128) :=
  P.onDegree (2, 128) modelH6SqClass

theorem pageH6_eq_basis (P : Presentation table A) :
    pageH6 E A P = P.basis (1, 64) h6_covered (0 : Fin 1) := by
  apply A.embed_injective (1, 64)
  calc
    A.embed (1, 64) (pageH6 E A P) = P.comparison modelX := by
      simpa [pageH6, modelH6Class] using (P.compatible (1, 64) modelH6Class).symm
    _ = A.embed (1, 64) (P.basis (1, 64) h6_covered (0 : Fin 1)) :=
      P.generator_image (1, 64) h6_covered (0 : Fin 1)

theorem pageH6Sq_eq_basis (P : Presentation table A) :
    pageH6Sq E A P = P.basis (2, 128) square_covered (0 : Fin 1) := by
  apply A.embed_injective (2, 128)
  calc
    A.embed (2, 128) (pageH6Sq E A P) = P.comparison modelY := by
      simpa [pageH6Sq, modelH6SqClass] using
        (P.compatible (2, 128) modelH6SqClass).symm
    _ = A.embed (2, 128) (P.basis (2, 128) square_covered (0 : Fin 1)) :=
      P.generator_image (2, 128) square_covered (0 : Fin 1)

/-- A SINGLE input bundles the existing sequence and the table's external
interpretation. The evidence is a parameter, not a new Lean axiom. -/
def myAdams
    (evidence : KIP126.External.ExternalEvidence (Nonempty (Presentation table A))) :
    Input where
  sequence := E
  algebra := A
  table := table
  tableCorrect := evidence
  h6_mem := h6_covered
  h6_dim := rfl

/-- The presentation theorem turns the numerical table entry into an equality
in the actual E₂ page of `E`. -/
theorem page_square (P : Presentation table A) :
    A.product (1, 64) (1, 64)
        (pageH6 E A P) (pageH6 E A P) = pageH6Sq E A P := by
  apply A.embed_injective (2, 128)
  calc
    A.embed (2, 128) (A.product (1, 64) (1, 64)
        (pageH6 E A P) (pageH6 E A P)) =
        A.embed (1, 64) (pageH6 E A P) * A.embed (1, 64) (pageH6 E A P) :=
      A.product_assembly (1, 64) (1, 64) _ _
    _ = P.comparison modelX * P.comparison modelX := by
      change A.embed (1, 64) (P.onDegree (1, 64) modelH6Class) *
        A.embed (1, 64) (P.onDegree (1, 64) modelH6Class) = _
      rw [← P.compatible (1, 64) modelH6Class]
      rfl
    _ = P.comparison (modelX * modelX) := (map_mul P.comparison modelX modelX).symm
    _ = P.comparison modelY := by rw [x_mul_x]
    _ = A.embed (2, 128) (pageH6Sq E A P) :=
      P.compatible (2, 128) modelH6SqClass

theorem imported_h6_square
    (evidence : KIP126.External.ExternalEvidence (Nonempty (Presentation table A))) :
    (myAdams E A evidence).h6Square =
      (myAdams E A evidence).presentation.basis
        (2, 128) square_covered (0 : Fin 1) := by
  have h := (myAdams E A evidence).presentation.basis_mul (1, 64) (1, 64)
    h6_covered h6_covered square_covered (0 : Fin 1) (0 : Fin 1)
  change (myAdams E A evidence).h6Square =
    ∑ k : Fin 1, (1 : F2) •
      (myAdams E A evidence).presentation.basis (2, 128) square_covered k at h
  rw [Fintype.sum_unique, one_smul] at h
  have hi : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simpa only [hi] using h

theorem imported_h6_square_ne_zero
    (evidence : KIP126.External.ExternalEvidence (Nonempty (Presentation table A))) :
    (myAdams E A evidence).h6Square ≠ 0 := by
  rw [imported_h6_square]
  exact ((myAdams E A evidence).presentation.basis (2, 128) square_covered).ne_zero
    (0 : Fin 1)

#print axioms x_mul_x
#print axioms y_ne_zero
#print axioms x_mul_y_ne_zero
#print axioms page_square
#print axioms imported_h6_square
#print axioms imported_h6_square_ne_zero

end
end KIP126.Examples.AdamsE2Table
