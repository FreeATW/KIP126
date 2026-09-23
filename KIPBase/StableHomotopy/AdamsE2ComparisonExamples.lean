import KIPBase.StableHomotopy.AdamsE2Comparison
import KIPBase.E2pageTactic

/-!
将计算器验证的等式搬到既有球谱 Adams 第二页。
比较使用 AdamsE2Comparison 的显式外部公理；e2_mul 仍依赖尚未证明的
coordinateCheck_sound。此文件不添加公理或 sorry。
-/

set_option maxRecDepth 16384

namespace KIPBase.StableHomotopy.SphereAdamsE2.Examples

open SphereE2

private theorem generator_mem (i : Generator) :
    generator i ∈ homogeneousPart (generatorDegree i).1 (generatorDegree i).2 := by
  apply Submodule.subset_span
  refine ⟨Finsupp.single i 1, ?_, ?_⟩
  · simp [monomialDegree]
  · rfl

/-- 数据环中带有齐次次数的 h₀。 -/
noncomputable def dataH0 : E2At 1 1 :=
  ⟨h0, by exact generator_mem ⟨0, by decide⟩⟩

/-- 数据环中带有齐次次数的 h₁。 -/
noncomputable def dataH1 : E2At 1 2 :=
  ⟨h1, by exact generator_mem ⟨1, by decide⟩⟩

universe u v
variable (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]

/-- 实际第二页上的 h₀ 与 h₁ 的乘积在 A^{2,3} 中为零。 -/
example :
    pageMul 𝒮 1 1 1 2
      (comparison 𝒮 1 1 (by decide) dataH0)
      (comparison 𝒮 1 2 (by decide) dataH1) = 0 := by
  apply mul_eq_zero_of_data 𝒮 1 1 1 2 (by decide) (by decide) (by decide)
  change h0 * h1 = 0
  e2_mul

/-- 平方示例：两个 h₀ 的像相乘，等于数据环中 h₀² 的像。 -/
example :
    pageMul 𝒮 1 1 1 1
      (comparison 𝒮 1 1 (by decide) dataH0)
      (comparison 𝒮 1 1 (by decide) dataH0) =
    comparison 𝒮 2 2 (by decide)
      (mulAt (s := 1) (t := 1) (s' := 1) (t' := 1) dataH0 dataH0) := by
  apply mul_eq_of_data 𝒮 1 1 1 1 (by decide) (by decide) (by decide)
  change h0 * h0 = h0 * h0
  e2_mul

-- 范围限制不能被绕过：无法提供 t = 262 的比较或 t+t' = 262 的相容性。
example : True := by
  fail_if_success have := comparison 𝒮 1 262 (by omega)
  fail_if_success have := comparison_mul 𝒮 1 261 1 1 (by omega)
  trivial

end KIPBase.StableHomotopy.SphereAdamsE2.Examples
