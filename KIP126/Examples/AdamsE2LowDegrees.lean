import KIP126.Examples.AdamsE2LowDegrees.Data
import Mathlib.Tactic.Ring

/-!
# 使用林氏低次数数据表

数值输入位于 `AdamsE2LowDegrees/Data.lean`。本文件先由内核检查查询结果，
再根据数据表证明环中的关系，最后在显式表示证据的条件下，将乘法等式传递到
已有的实际 E₂ 页。前两步并不声称数值表就是球谱的实际 E₂ 页。
-/

namespace KIP126.Examples.AdamsE2LowDegrees

open KIP126.AdamsE2 KIP126.Core.Algebra KIP126.Classical.Adams

noncomputable section

theorem basis_count : basisRows.length = 27 := by rfl

-- 这里检查的是已导入的维数，并未重新计算 Ext。
example : table.dim (1, 1) = 1 := by rfl
example : table.dim (2, 3) = 0 := by rfl
example : table.dim (3, 11) = 1 := by rfl -- c₀，图上的坐标为 (8,3)
example : table.dim (2, 128) = 1 := by rfl
example : table.dim (5, 20) = 2 := by rfl

theorem h0_h1_zero : modelH0 * modelH1 = 0 := by
  apply table.generator_mul_eq_zero (1, 1) (1, 2) _ _
    (rectangle_mem 2 1 (by omega) (by omega) (by omega) (by omega))
  decide

theorem h1_h2_zero : modelH1 * modelH2 = 0 := by
  apply table.generator_mul_eq_zero (1, 2) (1, 4) _ _
    (rectangle_mem 2 4 (by omega) (by omega) (by omega) (by omega))
  decide

theorem h0_c0_zero : modelH0 * modelC0 = 0 := by
  apply table.generator_mul_eq_zero (1, 1) (3, 11) _ _
    (rectangle_mem 4 8 (by omega) (by omega) (by omega) (by omega))
  decide

theorem h0_square : modelH0 * modelH0 = modelH0Sq := by
  apply table.generator_mul_eq_generator (1, 1) (1, 1)
  decide

theorem h1_square : modelH1 * modelH1 = modelH1Sq := by
  apply table.generator_mul_eq_generator (1, 2) (1, 2)
  decide

theorem h0_times_h2 : modelH0 * modelH2 = modelH0H2 := by
  apply table.generator_mul_eq_generator (1, 1) (1, 4)
  decide

theorem h0Sq_times_h2 : modelH0Sq * modelH2 = modelH0SqH2 := by
  apply table.generator_mul_eq_generator (2, 2) (1, 4)
  decide

theorem h1_times_h1Sq : modelH1 * modelH1Sq = modelH0SqH2 := by
  apply table.generator_mul_eq_generator (1, 2) (2, 4)
  decide

/-- 一个非平凡关系：两个不同的单项式表达式表示同一元素。 -/
theorem h1_cube : modelH1 ^ 3 = modelH0 ^ 2 * modelH2 := by
  calc
    modelH1 ^ 3 = modelH1 * (modelH1 * modelH1) := by ring
    _ = modelH0SqH2 := by rw [h1_square, h1_times_h1Sq]
    _ = modelH0 ^ 2 * modelH2 := by rw [pow_two, h0_square, h0Sq_times_h2]

theorem h1_times_h3 : modelH1 * modelH3 = modelH1H3 := by
  apply table.generator_mul_eq_generator (1, 2) (1, 8)
  decide

theorem h6_square : modelH6 * modelH6 = modelH6Sq := by
  apply table.generator_mul_eq_generator (1, 64) (1, 64)
  decide

theorem h1_times_d0 : modelH1 * modelD0 = modelB0 := by
  apply table.generator_mul_eq_generator (1, 2) (4, 18)
  decide

theorem h0Sq_square : modelH0Sq * modelH0Sq = modelH0Fourth := by
  apply table.generator_mul_eq_generator (2, 2) (2, 2)
  decide

theorem h0_fourth : modelH0 ^ 4 = modelH0Fourth := by
  calc
    modelH0 ^ 4 = (modelH0 * modelH0) * (modelH0 * modelH0) := by ring
    _ = modelH0Fourth := by rw [h0_square, h0Sq_square]

theorem h0Fourth_times_h4 : modelH0Fourth * modelH4 = modelB1 := by
  apply table.generator_mul_eq_generator (4, 4) (1, 16)
  decide

theorem two_products_sum :
    modelH1 * modelD0 + modelH0Fourth * modelH4 = modelB0 + modelB1 := by
  rw [h1_times_d0, h0Fourth_times_h4]

theorem two_monomials_sum :
    modelH1 * modelD0 + modelH0 ^ 4 * modelH4 = modelB0 + modelB1 := by
  rw [h0_fourth, two_products_sum]

variable (E : ClassicalAdamsSpectralSequence) (A : PageAlgebra E)

/-- 把模型环中一个有指定次数的形式基元看成该次数的齐次元素。 -/
def modelClass (p : Degree) (hp : p ∈ table.region) (i : Fin (table.dim p)) :
    table.piece p :=
  ⟨table.generator p hp i, table.generator_mem_piece p hp i⟩

/-- 给定一个关于真实 `E₂` 页的表示定理后，把模型基元映到该页。 -/
def pageClass (P : Presentation table A) (p : Degree) (hp : p ∈ table.region)
    (i : Fin (table.dim p)) : Page E p :=
  P.onDegree p (modelClass p hp i)

/-- `pageClass` 的值确实是表示定理给出的页上基向量。
这是模型环与真实 `E₂` 之间的桥，而不是对 `E₂` 的重新定义。 -/
theorem pageClass_eq_basis (P : Presentation table A) (p : Degree)
    (hp : p ∈ table.region) (i : Fin (table.dim p)) :
    pageClass E A P p hp i = P.basis p hp i := by
  apply A.embed_injective p
  calc
    A.embed p (pageClass E A P p hp i) =
        P.comparison (table.generator p hp i) := by
      simpa [pageClass, modelClass] using (P.compatible p (modelClass p hp i)).symm
    _ = A.embed p (P.basis p hp i) := P.generator_image p hp i

/-- 以下类都是在给定 `Presentation` 后，从模型环映入真实 `E₂` 的元素。 -/
def pageH0 (P : Presentation table A) : Page E (1, 1) :=
  pageClass E A P (1, 1)
    (rectangle_mem 1 0 (by omega) (by omega) (by omega) (by omega)) ⟨0, by decide⟩

def pageH1 (P : Presentation table A) : Page E (1, 2) :=
  pageClass E A P (1, 2)
    (rectangle_mem 1 1 (by omega) (by omega) (by omega) (by omega)) ⟨0, by decide⟩

def pageH1Sq (P : Presentation table A) : Page E (2, 4) :=
  pageClass E A P (2, 4)
    (rectangle_mem 2 2 (by omega) (by omega) (by omega) (by omega)) ⟨0, by decide⟩

def pageH0SqH2 (P : Presentation table A) : Page E (3, 6) :=
  pageClass E A P (3, 6)
    (rectangle_mem 3 3 (by omega) (by omega) (by omega) (by omega)) ⟨0, by decide⟩

def pageH0Fourth (P : Presentation table A) : Page E (4, 4) :=
  pageClass E A P (4, 4)
    (rectangle_mem 4 0 (by omega) (by omega) (by omega) (by omega)) ⟨0, by decide⟩

def pageH4 (P : Presentation table A) : Page E (1, 16) :=
  pageClass E A P (1, 16) (exceptional_mem _ (Or.inr (Or.inr (Or.inl rfl))))
    ⟨0, by decide⟩

def pageD0 (P : Presentation table A) : Page E (4, 18) :=
  pageClass E A P (4, 18) (exceptional_mem _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    ⟨0, by decide⟩

def pageB0 (P : Presentation table A) : Page E (5, 20) :=
  pageClass E A P (5, 20) (exceptional_mem _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    ⟨0, by decide⟩

def pageB1 (P : Presentation table A) : Page E (5, 20) :=
  pageClass E A P (5, 20) (exceptional_mem _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    ⟨1, by decide⟩

def pageH6 (P : Presentation table A) : Page E (1, 64) :=
  pageClass E A P (1, 64) (exceptional_mem _ (Or.inl rfl)) ⟨0, by decide⟩

def pageH6Sq (P : Presentation table A) : Page E (2, 128) :=
  pageClass E A P (2, 128) (exceptional_mem _ (Or.inr (Or.inl rfl))) ⟨0, by decide⟩

/-- 真实页上的平方使用页自身的乘法，而不是再导入一个同名元素。 -/
def pageH6Square (P : Presentation table A) : Page E (2, 128) :=
  A.product (1, 64) (1, 64) (pageH6 E A P) (pageH6 E A P)

/-- 模型环中的 `modelH6 * modelH6 = modelH6Sq` 通过表示同态
变成真实 `E₂` 页上的乘法等式。 -/
theorem page_h6_square_from_model (P : Presentation table A) :
    pageH6Square E A P = pageH6Sq E A P := by
  apply A.embed_injective (2, 128)
  calc
    A.embed (2, 128) (pageH6Square E A P) =
        A.embed (1, 64) (pageH6 E A P) * A.embed (1, 64) (pageH6 E A P) :=
      A.product_assembly (1, 64) (1, 64) _ _
    _ = P.comparison modelH6 * P.comparison modelH6 := by
      change A.embed (1, 64) (P.onDegree (1, 64)
          (modelClass (1, 64) (exceptional_mem _ (Or.inl rfl)) ⟨0, by decide⟩)) *
        A.embed (1, 64) (P.onDegree (1, 64)
          (modelClass (1, 64) (exceptional_mem _ (Or.inl rfl)) ⟨0, by decide⟩)) = _
      rw [← P.compatible (1, 64)
        (modelClass (1, 64) (exceptional_mem _ (Or.inl rfl)) ⟨0, by decide⟩)]
      simp only [modelClass, modelH6]
    _ = P.comparison (modelH6 * modelH6) :=
      (map_mul P.comparison modelH6 modelH6).symm
    _ = P.comparison modelH6Sq := by rw [h6_square]
    _ = A.embed (2, 128) (pageH6Sq E A P) :=
      P.compatible (2, 128)
        (modelClass (2, 128) (exceptional_mem _ (Or.inr (Or.inl rfl)))
          ⟨0, by decide⟩)

/-- 将这张较大的表接入已有对象，不重新构造 E₂ 或谱序列。 -/
def myAdams
    (evidence : KIP126.External.ExternalEvidence (Nonempty (Presentation table A))) :
    Input where
  sequence := E
  algebra := A
  table := table
  tableCorrect := evidence
  h6_mem := exceptional_mem _ (Or.inl rfl)
  h6_dim := by decide

theorem page_h0_h1_zero (P : Presentation table A) :
    A.product (1, 1) (1, 2)
      (pageH0 E A P) (pageH1 E A P) = 0 := by
  rw [pageH0, pageH1, pageClass_eq_basis, pageClass_eq_basis]
  apply P.basis_mul_eq_zero _ _ _ _
    (rectangle_mem 2 1 (by omega) (by omega) (by omega) (by omega))
  decide

/-- 将表中关系 h₁·h₁² = h₀²h₂ 解释为实际 E₂ 页在 (3,6) 分量中的等式。 -/
theorem page_h1_times_h1Sq (P : Presentation table A) :
    A.product (1, 2) (2, 4)
      (pageH1 E A P) (pageH1Sq E A P) = pageH0SqH2 E A P := by
  rw [pageH1, pageH1Sq, pageH0SqH2, pageClass_eq_basis,
    pageClass_eq_basis, pageClass_eq_basis]
  apply P.basis_mul_eq_basis
  decide

theorem page_h1_times_d0 (P : Presentation table A) :
    A.product (1, 2) (4, 18)
      (pageH1 E A P) (pageD0 E A P) = pageB0 E A P := by
  rw [pageH1, pageD0, pageB0, pageClass_eq_basis,
    pageClass_eq_basis, pageClass_eq_basis]
  apply P.basis_mul_eq_basis
  decide

theorem page_h0Fourth_times_h4 (P : Presentation table A) :
    A.product (4, 4) (1, 16)
      (pageH0Fourth E A P) (pageH4 E A P) = pageB1 E A P := by
  rw [pageH0Fourth, pageH4, pageB1, pageClass_eq_basis,
    pageClass_eq_basis, pageClass_eq_basis]
  apply P.basis_mul_eq_basis
  decide

/-- 这两个不同的乘积线性无关，而不是同一个类的两个名称。
对它们的和应用基坐标映射，得到向量 [1,1]。 -/
theorem page_two_products_sum_ne_zero (P : Presentation table A) :
    Add.add (α := Page E (5, 20))
      (A.product (1, 2) (4, 18)
        (pageH1 E A P) (pageD0 E A P))
      (A.product (4, 4) (1, 16)
        (pageH0Fourth E A P) (pageH4 E A P)) ≠ 0 := by
  rw [page_h1_times_d0, page_h0Fourth_times_h4]
  rw [pageB0, pageB1, pageClass_eq_basis, pageClass_eq_basis]
  let b : Module.Basis (Fin 2) F2 (Page E (5, 20)) :=
    P.basis (5, 20) (exceptional_mem _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  change b 0 + b 1 ≠ 0
  intro h
  have hc := congrArg (fun x => b.repr x 0) h
  simp at hc

theorem imported_h6_square
    (evidence : KIP126.External.ExternalEvidence (Nonempty (Presentation table A))) :
    (myAdams E A evidence).h6Square =
      (myAdams E A evidence).presentation.basis (2, 128)
        (exceptional_mem _ (Or.inr (Or.inl rfl)))
        ⟨0, by change 0 < dim (2, 128); decide⟩ := by
  apply (myAdams E A evidence).presentation.basis_mul_eq_basis (1, 64) (1, 64)
  change ∀ l : Fin (dim (2, 128)),
    coefficient (1, 64) (1, 64) ⟨0, by decide⟩ ⟨0, by decide⟩ l =
      if l = ⟨0, by decide⟩ then 1 else 0
  decide

theorem imported_h6_square_ne_zero
    (evidence : KIP126.External.ExternalEvidence (Nonempty (Presentation table A))) :
    (myAdams E A evidence).h6Square ≠ 0 := by
  rw [imported_h6_square]
  exact ((myAdams E A evidence).presentation.basis (2, 128)
    (exceptional_mem _ (Or.inr (Or.inl rfl)))).ne_zero _

#print axioms h1_cube
#print axioms page_h6_square_from_model
#print axioms page_h1_times_h1Sq
#print axioms page_two_products_sum_ne_zero
#print axioms imported_h6_square_ne_zero

end
end KIP126.Examples.AdamsE2LowDegrees
