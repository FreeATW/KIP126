import KIPBase.E2pageTactic

/-!
自动化证明示例。这里的等式证明依赖暂留 sorry 的 coordinateCheck_sound，
并非已经完成形式化认证；具体坐标检查由 e2_mul 实际执行。
失败回归确保不等坐标、错误类型、未知变量和超范围计算不会被 tactic 接受。
-/
namespace KIPBase.SphereE2

example : h0 * h1 = 0 := by e2_mul
example : h1 ^ 3 = h0 ^ 2 * h2 := by e2_mul
example : (h0 + h1) * h1 = h1 ^ 2 := by e2_mul

-- 两个因子都是总 E₂ 代数中的一般元素（非齐次的和），不是单个生成元。
-- 展开后交叉项由 h₀h₁ = 0 消失，再用 h₁³ = h₀²h₂ 约化。
example : (h0 ^ 2 + h1 ^ 2) * (h0 + h1) = h0 ^ 3 + h0 ^ 2 * h2 := by
  e2_mul

-- 接受任意具体生成元编号，此处编号 4 是 c₀。
example : h0 * generator ⟨4, by decide⟩ = 0 := by e2_mul

-- 后续证明中直接使用 have；允许局部 let 和可展开的命名常量。
example : h1 ^ 3 * h0 = 0 := by
  have hc : h1 ^ 3 = h0 ^ 2 * h2 := by e2_mul
  rw [hc]
  e2_mul

example : True := by
  -- 失败必须保留目标；不同双次数的基 index=0 不能误判为相等。
  fail_if_success have : h0 = h1 := by e2_mul
  fail_if_success have : h1 ^ 2 = 0 := by e2_mul
  fail_if_success have : (1 : Nat) = 1 := by e2_mul
  fail_if_success have : h0 ^ 262 = 0 := by e2_mul
  fail_if_success have : h0 * h1 = 0 := by e2_mul 0
  trivial

example (_x : E2) : True := by
  fail_if_success have : _x * h0 = 0 := by e2_mul
  trivial

example : h0 * h1 = 0 := by
  let a := h0
  change a * h1 = 0
  e2_mul

-- 系数、单位、零次幂和非齐次加法。
example : (2 : E2) * h0 = 0 := by e2_mul
example : (1 : E2) * h0 = h0 := by e2_mul
example : h0 ^ 0 = 1 := by e2_mul
example : h0 + h1 = h1 + h0 := by e2_mul

end KIPBase.SphereE2
