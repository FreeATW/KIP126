import KIP126.Def.AdamsE2
import Mathlib.Data.Int.Interval

/-!
# 带有明确来源和非平凡乘法的 Adams E₂ 数据表

来源：林伟南，《模 2 Steenrod 代数的上同调》，版本 t261.2，
https://doi.org/10.5281/zenodo.7865526，文件 `S0_AdamsE2_csv.zip`。
SHA-256 校验值：bb53d84a3450d58535f7119d3a4fa2123688f9574c396d592763c37be89de470。

图上的矩形范围为 0 ≤ s ≤ 8、0 ≤ t-s ≤ 8，其中 t-s 为稳定茎次数。
另外保留 (1,64)、(2,128)，并加入 (1,16)、(4,18)、(5,20)，以展示二维格点。
所有存储的次数均为内部双次数 (s,t)，不是图上的坐标 (t-s,s)。
保留源数据中的基编号；乘法记录由已发表的关系化简得到，不是仅根据维数推测。

可用 `scripts/extract_adams_e2_low.py` 重现带标记的数据区块。
这些数值数据本身并不证明它们描述了球谱的实际页；这一解释仍须由显式输入
`ExternalEvidence (Nonempty (Presentation table A))` 提供。
-/

namespace KIP126.Examples.AdamsE2LowDegrees

open KIP126.AdamsE2 KIP126.Core.Algebra

-- 林氏 CSV 提取数据开始
/-- CSV 中的基编号、内部双次数和便于阅读的单项式名称。 -/
def basisRows : List (Nat × Degree × String) :=
  [
    (0, (0, 0), "1"),
    (1, (1, 1), "h_0"),
    (2, (2, 2), "h_0^2"),
    (3, (1, 2), "h_1"),
    (4, (3, 3), "h_0^3"),
    (5, (4, 4), "h_0^4"),
    (6, (2, 4), "h_1^2"),
    (7, (1, 4), "h_2"),
    (8, (5, 5), "h_0^5"),
    (9, (2, 5), "h_0 * h_2"),
    (10, (6, 6), "h_0^6"),
    (11, (3, 6), "h_0^2 * h_2"),
    (12, (7, 7), "h_0^7"),
    (13, (8, 8), "h_0^8"),
    (14, (2, 8), "h_2^2"),
    (15, (1, 8), "h_3"),
    (17, (2, 9), "h_0 * h_3"),
    (19, (3, 10), "h_0^2 * h_3"),
    (20, (2, 10), "h_1 * h_3"),
    (22, (4, 11), "h_0^3 * h_3"),
    (23, (3, 11), "c_0"),
    (35, (1, 16), "h_4"),
    (42, (4, 18), "d_0"),
    (50, (5, 20), "h_1 * d_0"),
    (51, (5, 20), "h_0^4 * h_4"),
    (401, (1, 64), "h_6"),
    (2314, (2, 128), "h_6^2")
  ]

/-- 目标在覆盖范围内且不含单位因子的全部非零乘积；编号对应 basisRows。 -/
def productRows : List (Nat × Nat × List Nat) :=
  [
    (1, 1, [2]),
    (1, 2, [4]),
    (1, 4, [5]),
    (1, 5, [8]),
    (1, 7, [9]),
    (1, 8, [10]),
    (1, 9, [11]),
    (1, 10, [12]),
    (1, 12, [13]),
    (1, 15, [17]),
    (1, 17, [19]),
    (1, 19, [22]),
    (2, 2, [5]),
    (2, 4, [8]),
    (2, 5, [10]),
    (2, 7, [11]),
    (2, 8, [12]),
    (2, 10, [13]),
    (2, 15, [19]),
    (2, 17, [22]),
    (3, 3, [6]),
    (3, 6, [11]),
    (3, 15, [20]),
    (3, 42, [50]),
    (4, 4, [10]),
    (4, 5, [12]),
    (4, 8, [13]),
    (4, 15, [22]),
    (5, 5, [13]),
    (5, 35, [51]),
    (7, 7, [14]),
    (401, 401, [2314])
  ]
-- 共覆盖 86 个格点；各维数的格点数量为 {0: 60, 1: 25, 2: 1}。
-- 共 27 个基向量；已检查覆盖范围内的 142 个无序乘积（包括单位乘积）。
-- 林氏 CSV 提取数据结束

/-- 显式包含零维格点；只有在此已声明且完整提取的区域内，
缺少基记录才表示该格点为零维。 -/
def region : Finset Degree :=
  ((Finset.Icc (0 : ℤ) 8 ×ˢ Finset.Icc (0 : ℤ) 8).image
    (fun p => (p.1, p.1 + p.2))) ∪ {(1, 64), (2, 128), (1, 16), (4, 18), (5, 20)}

def basisIds (p : Degree) : List Nat :=
  (basisRows.filter (fun row => row.2.1 == p)).map Prod.fst

def dim (p : Degree) : Nat := (basisIds p).length

/-- 内部查询，仅在确认次数位于覆盖范围内、基下标合法后调用。
源数据提取过程先检查全部覆盖范围内的基对，再省略零乘积。 -/
def productIds (left right : Nat) : List Nat :=
  if left = 0 then [right]
  else if right = 0 then [left]
  else ((productRows.find? (fun row =>
    row.1 == min left right && row.2.1 == max left right)).map (·.2.2)).getD []

def coefficient (p q : Degree) (i : Fin (dim p)) (j : Fin (dim q))
    (k : Fin (dim (p + q))) : F2 :=
  if (basisIds (p + q))[k] ∈ productIds (basisIds p)[i] (basisIds q)[j] then 1 else 0

/-- 低次矩形中格点的成员证明不展开整个已枚举的 `Finset`。 -/
theorem rectangle_mem (s n : ℤ) (hs0 : 0 ≤ s) (hs8 : s ≤ 8)
    (hn0 : 0 ≤ n) (hn8 : n ≤ 8) : (s, s + n) ∈ region := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨(s, n), ?_, rfl⟩
  simp only [Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hs0, hs8⟩, ⟨hn0, hn8⟩⟩

/-- 矩形外手动保留的五个格点。 -/
theorem exceptional_mem (p : Degree)
    (hp : p = (1, 64) ∨ p = (2, 128) ∨ p = (1, 16) ∨ p = (4, 18) ∨ p = (5, 20)) :
    p ∈ region := by
  apply Finset.mem_union_right
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

def table : Table where
  region := region
  dim := dim
  mulCoeff := fun p q _ _ _ => coefficient p q
  zero_mem := rectangle_mem 0 0 (by omega) (by omega) (by omega) (by omega)
  unitCoeff := fun i => if (basisIds (0, 0))[i] = 0 then 1 else 0

/-- 面向使用者的查询：`none` 表示未知、超出范围或输入不合法；
`some []` 表示已覆盖的零维目标空间中的零向量。 -/
def productCoordinates (p q : Degree) (i j : Nat) : Option (List Nat) :=
  if p ∈ region ∧ q ∈ region ∧ p + q ∈ region then
    if hi : i < dim p then
      if hj : j < dim q then
        some ((basisIds (p + q)).map (fun id =>
          if id ∈ productIds (basisIds p)[i] (basisIds q)[j] then 1 else 0))
      else none
    else none
  else none

noncomputable section

/-- 由导入的生成元和乘法关系定义的模型环。它不是谱序列的 `E₂` 页。 -/
abbrev ModelRing := table.Model

/-- 以 `model` 为前缀的类都只属于 `ModelRing`。
给定 `Presentation` 后，才能把它们映到真实 `E₂` 页。 -/
def modelH0 : ModelRing :=
  table.generator (1, 1) (rectangle_mem 1 0 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH1 : ModelRing :=
  table.generator (1, 2) (rectangle_mem 1 1 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH2 : ModelRing :=
  table.generator (1, 4) (rectangle_mem 1 3 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH3 : ModelRing :=
  table.generator (1, 8) (rectangle_mem 1 7 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelC0 : ModelRing :=
  table.generator (3, 11) (rectangle_mem 3 8 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH6 : ModelRing :=
  table.generator (1, 64) (exceptional_mem _ (Or.inl rfl)) ⟨0, by decide⟩
def modelH0Sq : ModelRing :=
  table.generator (2, 2) (rectangle_mem 2 0 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH1Sq : ModelRing :=
  table.generator (2, 4) (rectangle_mem 2 2 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH0H2 : ModelRing :=
  table.generator (2, 5) (rectangle_mem 2 3 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH0SqH2 : ModelRing :=
  table.generator (3, 6) (rectangle_mem 3 3 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH1H3 : ModelRing :=
  table.generator (2, 10) (rectangle_mem 2 8 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelH6Sq : ModelRing :=
  table.generator (2, 128) (exceptional_mem _ (Or.inr (Or.inl rfl))) ⟨0, by decide⟩
def modelH4 : ModelRing :=
  table.generator (1, 16) (exceptional_mem _ (Or.inr (Or.inr (Or.inl rfl))))
    ⟨0, by decide⟩
def modelD0 : ModelRing :=
  table.generator (4, 18) (exceptional_mem _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    ⟨0, by decide⟩
def modelH0Fourth : ModelRing :=
  table.generator (4, 4) (rectangle_mem 4 0 (by omega) (by omega) (by omega) (by omega))
    ⟨0, by decide⟩
def modelB0 : ModelRing :=
  table.generator (5, 20) (exceptional_mem _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    ⟨0, by decide⟩
def modelB1 : ModelRing :=
  table.generator (5, 20) (exceptional_mem _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    ⟨1, by decide⟩

end

end KIP126.Examples.AdamsE2LowDegrees
