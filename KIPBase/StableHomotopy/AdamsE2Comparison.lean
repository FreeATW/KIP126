import KIPBase.StableHomotopy.Adams
import KIPBase.E2page

/-!
# 球谱 Adams E₂ 与 Zenodo 计算环的范围内比较

按用户要求，本模块使用显式 axiom 接入外部数学结果。来源为
https://zenodo.org/records/14875701，v126.3.cw49 的 S0 Adams E₂ 数据。
完整原始 CSV 的摘要、生成元和关系见 KIPBase.E2pageData。

目标始终是既有 `AdamsSS 𝒮 SphereSpectrum` 的真实 Page 2 对象，
不是通过计算环重新定义的谱序列或第二页。

这里选择非负双次数 (s,t)，并只对内部次数 t ≤ 261 声明比较同构。
乘法相容性要求 t+t' ≤ 261；不把计算环的高次截断零关系传到完整第二页。
不声明从整个截断环到完整第二页总代数的环同态。

新增外部假设：pageModule、pageMul、comparison、comparison_mul。
只提供第二页的双线性乘法及其范围内比较；不补充后续微分、各页乘法、
Leibniz 法则或收敛断言。下方搬运定理的证明没有新增 sorry；
数据乘法 mulAt 仍使用既有 multiply_mem 的 sorry。
-/

namespace KIPBase.StableHomotopy.SphereAdamsE2

universe u v

variable (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]

/-- 球谱既有 Adams 谱序列的 (s,t) 第二页分量。 -/
abbrev Page (s t : ℕ) : Type v :=
  (AdamsSS 𝒮 (SphereSpectrum : 𝒮)).Page 2 ((s : ℤ), (t : ℤ))

/-- 外部结构：第二页的 F₂ 模结构，使用其已有加法群结构。 -/
axiom pageModule (s t : ℕ) : Module SphereE2.F2 (Page 𝒮 s t)

noncomputable instance (s t : ℕ) : Module SphereE2.F2 (Page 𝒮 s t) :=
  pageModule 𝒮 s t

/-- 外部结构：球谱 Adams 第二页的双线性乘法。
此乘法作用于实际的 Page 2 分量；比较公理仅约束数据覆盖范围内的乘积。 -/
axiom pageMul (s t s' t' : ℕ) :
  Page 𝒮 s t →ₗ[SphereE2.F2]
    Page 𝒮 s' t' →ₗ[SphereE2.F2] Page 𝒮 (s + s') (t + t')

/-- 外部计算比较：D^{s,t} ≃ A^{s,t}，只在内部次数 t ≤ 261 提供。
D 是现有 SphereE2.E2 截断商环，D^{s,t} 是其 homogeneousPart。
这是选择了一个同构见证，比单纯 Nonempty 更便于后续引用。 -/
axiom comparison (s t : ℕ) (ht : t ≤ 261) :
  SphereE2.E2At s t ≃ₗ[SphereE2.F2] Page 𝒮 s t

/-- 外部计算比较保持乘法；目标次数必须仍在计算范围内。 -/
axiom comparison_mul (s t s' t' : ℕ) (h : t + t' ≤ 261)
    (x : SphereE2.E2At s t) (y : SphereE2.E2At s' t') :
    comparison 𝒮 (s + s') (t + t') h (SphereE2.mulAt x y) =
      pageMul 𝒮 s t s' t'
        (comparison 𝒮 s t (by omega) x)
        (comparison 𝒮 s' t' (by omega) y)

/-- 所有实际第二页元素都有范围内的数据模型原像。 -/
theorem exists_data_preimage (s t : ℕ) (ht : t ≤ 261) (a : Page 𝒮 s t) :
    ∃ x : SphereE2.E2At s t, comparison 𝒮 s t ht x = a :=
  ⟨(comparison 𝒮 s t ht).symm a, (comparison 𝒮 s t ht).apply_symm_apply a⟩

/-- 实际页上的相等性等价于计算商环中代表元素的相等性。 -/
theorem comparison_eq_iff (s t : ℕ) (ht : t ≤ 261)
    (x y : SphereE2.E2At s t) :
    comparison 𝒮 s t ht x = comparison 𝒮 s t ht y ↔
      (x : SphereE2.E2) = (y : SphereE2.E2) := by
  constructor
  · intro h
    exact congrArg Subtype.val ((comparison 𝒮 s t ht).injective h)
  · intro h
    exact congrArg (comparison 𝒮 s t ht) (Subtype.ext h)

/-- 将数据模型中的乘积等式搬到实际 Adams 第二页。
输入 ht、ht' 可以来自调用方；证明无关性使其与 comparison_mul 中的界证明相容。 -/
theorem mul_eq_of_data (s t s' t' : ℕ)
    (ht : t ≤ 261) (ht' : t' ≤ 261) (h : t + t' ≤ 261)
    (x : SphereE2.E2At s t) (y : SphereE2.E2At s' t')
    (z : SphereE2.E2At (s + s') (t + t'))
    (hdata : (x : SphereE2.E2) * (y : SphereE2.E2) = (z : SphereE2.E2)) :
    pageMul 𝒮 s t s' t' (comparison 𝒮 s t ht x) (comparison 𝒮 s' t' ht' y) =
      comparison 𝒮 (s + s') (t + t') h z := by
  rw [← comparison_mul 𝒮 s t s' t' h x y]
  apply congrArg (comparison 𝒮 (s + s') (t + t') h)
  apply Subtype.ext
  exact hdata

/-- 特别地，数据模型中的零乘积给出实际页中的零乘积。 -/
theorem mul_eq_zero_of_data (s t s' t' : ℕ)
    (ht : t ≤ 261) (ht' : t' ≤ 261) (h : t + t' ≤ 261)
    (x : SphereE2.E2At s t) (y : SphereE2.E2At s' t')
    (hdata : (x : SphereE2.E2) * (y : SphereE2.E2) = 0) :
    pageMul 𝒮 s t s' t' (comparison 𝒮 s t ht x) (comparison 𝒮 s' t' ht' y) = 0 := by
  simpa only [map_zero] using
    mul_eq_of_data 𝒮 s t s' t' ht ht' h x y 0 hdata

end KIPBase.StableHomotopy.SphereAdamsE2
