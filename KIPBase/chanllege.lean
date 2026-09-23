import KIPBase.StableHomotopy.AdamsE2Comparison

/-!
# h₆² 在球谱的经典模 2 Adams 谱序列中存活至 E∞

来源：Weinan Lin, Guozhen Wang, Zhouli Xu,
On the Last Kervaire Invariant Problem, Theorem 1.4 (= Theorem 7.1).
https://arxiv.org/html/2412.10879v2

沿用本仓库外部给定的 `AdamsSS 𝒮 SphereSpectrum` 和 E₂ 比较公理。
CSV 中编号 69 的生成元是 h₆，双次数为 (s,t) = (1,64)；
其平方的双次数是 (2,128)，对应 stem t-s = 126。

“存活”用同一个 Z∞ 代表元表达：它在 E₂ 中代表指定元素，
且在 E∞ = Z∞/B∞ 中的像非零。没有假设存在整个 E₂ 到 E∞ 的映射，
也没有把 E∞ 分量非零或单独 d₂ = 0 当作指定元素存活。

这里只陈述论文结论。主定理的证明按要求保留 sorry；
这不是从现有 E₂ 乘法数据推导出的存活性证明。
-/

set_option maxRecDepth 16384

namespace KIPBase.KervaireChallenge

open CategoryTheory
open StableHomotopy StableHomotopy.SphereAdamsE2
open SphereE2

universe u v

/-- 原始 CSV 的生成元编号，采用从 0 开始的索引。 -/
def h6Generator : Generator := ⟨69, by decide⟩

theorem h6Generator_name : generatorName h6Generator = "h_6" := by decide

theorem h6Generator_degree : generatorDegree h6Generator = (1, 64) := by decide

private theorem generator_mem (i : Generator) :
    generator i ∈ homogeneousPart (generatorDegree i).1 (generatorDegree i).2 := by
  apply Submodule.subset_span
  refine ⟨Finsupp.single i 1, ?_, ?_⟩
  · simp [monomialDegree]
  · rfl

/-- 计算环 D 中的 h₆，附带其齐次次数。 -/
noncomputable def dataH6 : E2At 1 64 :=
  ⟨generator h6Generator, by
    simpa only [h6Generator_degree] using generator_mem h6Generator⟩

/-- 计算环 D 中的 h₆²；内部次数 128 仍在数据比较范围内。 -/
noncomputable def dataH6Sq : E2At 2 128 :=
  mulAt (s := 1) (t := 64) (s' := 1) (t' := 64) dataH6 dataH6

variable (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]

/-- 通过已有比较同构得到的、实际球谱 Adams 第二页上的 h₆。 -/
noncomputable def h6 : Page 𝒮 1 64 :=
  comparison 𝒮 1 64 (by decide) dataH6

/-- 实际第二页上的乘积 h₆ · h₆，位于 E₂^{2,128}。 -/
noncomputable def h6Sq : Page 𝒮 2 128 :=
  pageMul 𝒮 1 64 1 64 (h6 𝒮) (h6 𝒮)

/-- 实际第二页的平方与计算环中的平方由既有乘法相容公理联系。 -/
theorem h6Sq_eq_comparison :
    h6Sq 𝒮 = comparison 𝒮 2 128 (by decide) dataH6Sq := by
  exact (comparison_mul 𝒮 1 64 1 64 (by decide) dataH6 dataH6).symm

/-- 指定 E₂ 元素存活至 E∞ 并保持非零。

`SSData` 使用相对页编号 n = (r-r₀).toNat；在 Adams 谱序列 r₀ = 2，
因此实际 E₂ 对应 n = 0，而非 SSData 的 n = 2。
使用 Z∞ ↪ Z_n → E₂ 和 Z∞ → E∞，确保两页上使用同一个代表元。
Z∞ 排除支持非零微分，E∞ 中非零排除成为边缘。
-/
def SurvivesToEInfty (s t : ℕ) (x : Page 𝒮 s t) : Prop :=
  let E := AdamsSS 𝒮 (SphereSpectrum : 𝒮)
  let D := E.ssData ((s : ℤ), (t : ℤ))
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  ∃ z : (Subobject.underlying.obj (D.Z ⊤) : AddCommGrpCat.{v}),
    (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) z = x ∧
      (D.pageπ ⊤) z ≠ 0

/-- Lin–Wang–Xu, Theorem 1.4 / 7.1：
h₆² 在球谱的经典模 2 Adams 谱序列中存活至 E∞^{2,128}，且非零。
谱序列和 E₂ 比较沿用已导入的外部公理；本结论的证明尚未形式化。 -/
theorem h6_sq_survives_to_eInfty :
    SurvivesToEInfty 𝒮 2 128 (h6Sq 𝒮) := by
  sorry

end KIPBase.KervaireChallenge
