import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Defs
import KIPBase.E2pageCompute

/-!
# 球谱 Adams E₂ 页：Zenodo CSV 给出的具体代数模型

来源：https://zenodo.org/records/14875701，版本 v126.3.cw49。
完整的 2914 个生成元、231848 条关系和 23822 个基元素保存在
`KIPBase.E2pageData`；该模块也记录原始 UTF-16 CSV 的 SHA-256。

本文件定义 F₂ 上的生成元—关系商代数，并截断到内部次数 t ≤ 261。
乘法是该商代数的实际乘法，不是任意给定的运算，也不使用 sorry 定义。
超范围乘积在截断模型中为零，不声称真实 Ext 中的该乘积为零。

`E2` 是总的截断代数，`E2At s t` 是它的 (s,t) 齐次分量。
`mulAt` 是双分次乘法。`basisElements` 可访问 CSV 列出的单项式。
本文件不证明 CSV 单项式是基，也不证明本模型与真实 Ext 同构。
唯一的 sorry 是齐次分量乘法闭合性；下方具体总代数乘法例子不依赖它。
没有定义后续微分、E₃ 页或整个谱序列。
-/

set_option maxRecDepth 16384

namespace KIPBase.SphereE2

abbrev F2 := ZMod 2
abbrev Generator := Fin Data.generatorCount
abbrev Poly := MvPolynomial Generator F2

/-- CSV 的 (stem,s) 已在导入时转换成 (s,t)，其中 t = stem + s。 -/
def generatorDegree (i : Generator) : ℕ × ℕ :=
  let row := Data.generators[i.val]!
  (row.2.1, row.2.2)

def generatorName (i : Generator) : String :=
  (Data.generators[i.val]!).1

/-- 编码中的数字对 (生成元编号, 指数)。非法编号/奇数长度返回零。
导入时已逐行检查所有实际数据均合法；空列表表示单位单项式。 -/
noncomputable def polynomialOfPowers : List ℕ → Poly
  | [] => 1
  | i :: a :: rest =>
      if h : i < Data.generatorCount then
        MvPolynomial.X ⟨i, h⟩ ^ a * polynomialOfPowers rest
      else 0
  | [_] => 0

/-- 空字符串是单位；例如 "1,2,5,4" 表示 x₁² x₅⁴。
实际导入数据的所有数字字段已经过严格解析检查。 -/
noncomputable def monomialOfString (s : String) : Poly :=
  if s = "" then 1
  else polynomialOfPowers ((s.splitOn ",").map (fun n => n.toNat?.getD 0))

/-- 分号表示相加；关系字符串表示应当等于零的多项式。 -/
noncomputable def relationPolynomial (s : String) : Poly :=
  ((s.splitOn ";").map monomialOfString).sum

/-- 多重指数单项式的 (s,t) 双次数。 -/
def monomialDegree (m : Generator →₀ ℕ) : ℕ × ℕ :=
  m.sum fun i a => (a * (generatorDegree i).1, a * (generatorDegree i).2)

/-- 全部 CSV 关系，加上内部次数超过 261 的所有单项式。
后者明确实现截断，而不是把缺失数据理解成真实 Ext 中的零。 -/
noncomputable def definingRelations : Set Poly :=
  {p | (∃ code ∈ Data.relations, p = relationPolynomial code) ∨
       (∃ m : Generator →₀ ℕ,
         261 < (monomialDegree m).2 ∧ p = MvPolynomial.monomial m 1)}

noncomputable def definingIdeal : Ideal Poly := Ideal.span definingRelations

/-- 数据给出的具体截断 E₂ 代数。环和 F₂-代数实例由商代数继承。 -/
abbrev E2 := Poly ⧸ definingIdeal

noncomputable def projection : Poly →+* E2 := Ideal.Quotient.mk definingIdeal

/-- 指定编号的生成元在 E₂ 中的类。 -/
noncomputable def generator (i : Generator) : E2 := projection (MvPolynomial.X i)

/-- 总代数的乘法；也可直接使用 a * b。 -/
noncomputable def multiply (a b : E2) : E2 := a * b

/-- 一个 (s,t) 分量，由该次数的所有单项式的像张成。
这个定义不需要假设 CSV 中列出的单项式已经是基。 -/
noncomputable def homogeneousPart (s t : ℕ) : Submodule F2 E2 :=
  Submodule.span F2 {x | ∃ m : Generator →₀ ℕ,
    monomialDegree m = (s, t) ∧ x = projection (MvPolynomial.monomial m 1)}

/-- 具体页对象 E₂^{s,t}，自带 F₂ 向量空间结构。 -/
abbrev E2At (s t : ℕ) := ↥(homogeneousPart s t)

/-- 双分次乘法的闭合性。暂留证明，按用户要求使用 sorry。
这不是乘法的定义；底层乘法已经由 definingIdeal 的商环确定。 -/
theorem multiply_mem {s t s' t' : ℕ} {a b : E2}
    (ha : a ∈ homogeneousPart s t) (hb : b ∈ homogeneousPart s' t') :
    a * b ∈ homogeneousPart (s + s') (t + t') := by
  sorry

/-- E₂^{s,t} × E₂^{s',t'} → E₂^{s+s',t+t'}。 -/
noncomputable def mulAt {s t s' t' : ℕ}
    (a : E2At s t) (b : E2At s' t') : E2At (s + s') (t + t') :=
  ⟨a.val * b.val, multiply_mem a.property b.property⟩

/-! CSV 基表的访问：这里的 “basis” 是数据源的命名，不是已证明的 Basis。 -/

structure BasisRow where
  s : ℕ
  t : ℕ
  index : ℕ
  monomial : String
  deriving Inhabited, Repr

private def decodeBasisRow (line : String) : BasisRow :=
  let fields := line.splitOn "|"
  { s := (fields[0]!).toNat?.getD 0
    t := (fields[1]!).toNat?.getD 0
    index := (fields[2]!).toNat?.getD 0
    monomial := fields[3]! }

/-- 保留所有基表行；index 仅在各自双次数内编号。 -/
def basisRows : List BasisRow :=
  (Data.basisChunks.toList.flatMap (fun s => s.splitOn "\n")).map decodeBasisRow

noncomputable def basisValue (row : BasisRow) : E2 :=
  projection (monomialOfString row.monomial)

/-- 查询指定双次数中的全部基表单项式，保持 CSV 顺序。 -/
noncomputable def basisElements (s t : ℕ) : List E2 :=
  (basisRows.filter (fun row => row.s == s && row.t == t)).map basisValue

/-! 从真实 CSV 关系推出乘法等式。以下证明没有 sorry。 -/

/-- 任意 CSV 关系在商代数中为零。 -/
theorem csv_relation_zero (code : String) (h : code ∈ Data.relations) :
    projection (relationPolynomial code) = 0 := by
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  exact Ideal.subset_span (Or.inl ⟨code, h, rfl⟩)

private theorem first_relation_zero (code : String) (h : code ∈ Data.firstRelations) :
    projection (relationPolynomial code) = 0 :=
  csv_relation_zero code (List.mem_append_left _ h)

noncomputable def h0 : E2 := generator ⟨0, by decide⟩
noncomputable def h1 : E2 := generator ⟨1, by decide⟩
noncomputable def h2 : E2 := generator ⟨2, by decide⟩

/-- CSV 生成元 0,1,2 分别是 h₀,h₁,h₂，双次数为 (1,1),(1,2),(1,4)。 -/
example : generatorDegree ⟨0, by decide⟩ = (1, 1) ∧
    generatorDegree ⟨1, by decide⟩ = (1, 2) ∧
    generatorDegree ⟨2, by decide⟩ = (1, 4) := by decide

private theorem decode_monomial (code : String) (powers : List ℕ)
    (hne : code ≠ "")
    (h : (code.splitOn ",").map (fun n => n.toNat?.getD 0) = powers) :
    monomialOfString code = polynomialOfPowers powers := by
  simp only [monomialOfString, if_neg hne, h]

-- CSV 第 1 条关系："0,1,1,1"，即 h₀ h₁ = 0。
example : h0 * h1 = 0 := by
  have h := first_relation_zero "0,1,1,1" (by simp [Data.firstRelations])
  rw [relationPolynomial,
    show "0,1,1,1".splitOn ";" = ["0,1,1,1"] by native_decide] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [decode_monomial "0,1,1,1" [0,1,1,1] (by decide) (by native_decide)] at h
  simpa [polynomialOfPowers, Data.generatorCount, h0, h1, generator] using h

-- CSV 第 2 条关系："1,1,2,1"，即 h₁ h₂ = 0。
example : h1 * h2 = 0 := by
  have h := first_relation_zero "1,1,2,1" (by simp [Data.firstRelations])
  rw [relationPolynomial,
    show "1,1,2,1".splitOn ";" = ["1,1,2,1"] by native_decide] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [decode_monomial "1,1,2,1" [1,1,2,1] (by decide) (by native_decide)] at h
  simpa [polynomialOfPowers, Data.generatorCount, h1, h2, generator] using h

-- CSV 第 3 条关系："1,3;0,2,2,1"，即 h₁³ + h₀²h₂ = 0。
example : h1 ^ 3 + h0 ^ 2 * h2 = 0 := by
  have h := first_relation_zero "1,3;0,2,2,1" (by simp [Data.firstRelations])
  rw [relationPolynomial,
    show "1,3;0,2,2,1".splitOn ";" = ["1,3", "0,2,2,1"] by native_decide] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [decode_monomial "1,3" [1,3] (by decide) (by native_decide),
    decode_monomial "0,2,2,1" [0,2,2,1] (by decide) (by native_decide)] at h
  simpa [polynomialOfPowers, Data.generatorCount, h0, h1, h2, generator] using h

/-- 将计算器的稀疏多项式解释为原商代数中的元素。
可用于 `interpretComputedPolynomial result.normalForm`。
此函数不声称已形式化证明约化算法的正确性。 -/
noncomputable def interpretComputedPolynomial (p : Compute.PolynomialF2) : E2 :=
  (p.map fun m => projection
    (polynomialOfPowers (m.flatMap fun (i, a) => [i, a]))).sum

end KIPBase.SphereE2
