/-
  KIPBase.SpectralSequence.Crossing
  §2.7 Crossing predicates for spectral sequence differentials

  Blueprint: Definition 2.7 from arXiv:2412.10879 (KIP)
  Informal:  informal/crossing.md

  Defines the crossing predicate for spectral sequence differentials.
  All declarations are definitions — no theorems expected.
-/
import KIPBase.Mathlib
import KIPBase.SpectralSequence.Basic
import KIPBase.SpectralSequence.Convergence

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-! ### Essential differentials -/

/-- A differential `d r` at index `k` is **essential** if the morphism is nonzero. -/
def IsEssentialAt (E : SpectralSequence C ι) (r : ℤ) (k : ι) : Prop :=
  E.d r k ≠ 0

/-! ### The relation associated to a differential -/

/-- 微分 `d_r` 在双次数 `k` 处诱导的**关系**（d_r relation）：
    对广义元素 `x y : T ⟶ V`（`V` 为该双次数的环境对象），
    称 `x` 与 `y` 有 `d_r` 关系，当且仅当
    (1) `x` 落在 `d_r` 的定义域中——即 `x` 经过 `Z_r` 的包含分解
        （`d_r^k : E_r^k = Z_r/B_r ⟶ E_r^{k+deg}` 只定义在 `Z_r` 上）；
    (2) `y` 属于 `d_r(x)`——即 `y` 经过 `Z_{r}`（目标侧，同一 `Z` 塔的
        `r` 级子对象）的包含分解，且其在页 `E_r^{k+deg}` 中的像
        等于 `x` 经 `d_r` 的像。
    这里 `n = (r - E.r₀).toNat` 为页指标；`y ∈ d_r(x)` 按多值映射理解：
    `y` 是 `d_r` 在 `x` 处像集中的某个代表元（模 `B` 的歧义由
    「`y` 只需属于像」自动吸收）。 -/
def DifferentialRelation (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V) : Prop :=
  let n : WithTop ℕ := ↑(r - E.r₀).toNat
  ∃ (xZ : T ⟶ Subobject.underlying.obj ((E.ssData k).Z n)),
    xZ ≫ ((E.ssData k).Z n).arrow = x ∧
      ∃ (yZ : T ⟶ Subobject.underlying.obj ((E.ssData (k + E.diffDeg r)).Z n)),
        yZ ≫ ((E.ssData (k + E.diffDeg r)).Z n).arrow = y ∧
          xZ ≫ (E.ssData k).pageπ n ≫ E.d r k =
            yZ ≫ (E.ssData (k + E.diffDeg r)).pageπ n

/-- 微分 `d_r` 在双次数 `k` 处的**本质关系**（essential d_r relation）：
    `x` 与 `y` 有 `d_r` 关系，且 `y` 不在边缘子对象 `B_n` 中
    （即 `y` 不经过 `B_n` 分解，`n = (r - E.r₀).toNat` 为页指标）。
    这排除掉「像落在边界里」的退化情形，对应谱序列中
    微分像真正产生新同调类的情形。 -/
def EssentialDifferentialRelation (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V) : Prop :=
  DifferentialRelation E r k x y ∧
    ¬ Subobject.Factors ((E.ssData (k + E.diffDeg r)).B (↑(r - E.r₀).toNat : WithTop ℕ)) y

/-- 环境对象 `V` 中的元素与页 `E_r` 中的元素的**关联关系**：
    称 `x : T ⟶ V` 与页元素 `a : T ⟶ E_r` 关联，当且仅当
    存在提升 `xZ : T ⟶ Z_r` 使得 `xZ ≫ Z.arrow = x`（`x` 落在 `Z_r` 中）
    且 `xZ ≫ pageπ = a`（`a` 是 `x` 在页中的像）。
    这是「`x` 代表页类 `a`」的广义元素表述。 -/
def ElementPageRel (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (a : T ⟶ (E.ssData k).page (↑(r - E.r₀).toNat : WithTop ℕ)) : Prop :=
  ∃ (xZ : T ⟶ Subobject.underlying.obj
      ((E.ssData k).Z (↑(r - E.r₀).toNat : WithTop ℕ))),
    xZ ≫ ((E.ssData k).Z (↑(r - E.r₀).toNat : WithTop ℕ)).arrow = x ∧
      xZ ≫ (E.ssData k).pageπ (↑(r - E.r₀).toNat : WithTop ℕ) = a

/-- **d_r 的像刻画定理**（严格按「关联」语言表述）：
    `d_r(x) = y` 当且仅当存在页元素 `x₀ y₀` 使 `x₀` 与 `y₀` 有
    `d_r` 关系（页层面等式 `x₀ ≫ d_r = y₀`），且 `x` 与 `x₀` 关联、
    `y` 与 `y₀` 关联。 -/
theorem dr_apply_iff_rel (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V) :
    (∃ (x₀ : T ⟶ (E.ssData k).page (↑(r - E.r₀).toNat : WithTop ℕ))
        (y₀ : T ⟶ (E.ssData (k + E.diffDeg r)).page (↑(r - E.r₀).toNat : WithTop ℕ)),
      x₀ ≫ E.d r k = y₀ ∧
        ElementPageRel E r k x x₀ ∧
        ElementPageRel E r (k + E.diffDeg r) y y₀) ↔
      DifferentialRelation E r k x y := by
  constructor
  · rintro ⟨x₀, y₀, hxy, ⟨xZ, hxZ, hx₀⟩, ⟨yZ, hyZ, hy₀⟩⟩
    subst hx₀
    subst hy₀
    exact ⟨xZ, hxZ, yZ, hyZ, by rw [←Category.assoc]; exact hxy⟩
  · rintro ⟨xZ, hxZ, yZ, hyZ, hrel⟩
    exact ⟨xZ ≫ (E.ssData k).pageπ (↑(r - E.r₀).toNat : WithTop ℕ),
      yZ ≫ (E.ssData (k + E.diffDeg r)).pageπ (↑(r - E.r₀).toNat : WithTop ℕ),
      by rwa [Category.assoc], ⟨xZ, hxZ, rfl⟩, ⟨yZ, hyZ, rfl⟩⟩

/-- 一条 `d_r` 关系被另一条**本质关系** crossing：
    存在源双次数 `k'` 上的广义元素 `x' y'`，它们之间有
    `d_m` 本质关系（`EssentialDifferentialRelation`），且其过滤次数满足
    `filtDeg k' = filtDeg k + a`（`a > 0`，源在更高过滤）且
    `filtDeg (k' + diffDeg m) ≤ filtDeg k + r`（目标过滤不超过
    原关系的目标过滤）。 -/
def RelationCrossedBy (E : SpectralSequence C ι)
    (filtDeg : ι → ℤ) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V)
    (_h : DifferentialRelation E r k x y) : Prop :=
  ∃ (a : ℤ) (_ : 0 < a) (m : ℤ) (k' : ι)
    (x' : T ⟶ (E.ssData k').V)
    (y' : T ⟶ (E.ssData (k' + E.diffDeg m)).V),
    filtDeg k' = filtDeg k + a ∧
      EssentialDifferentialRelation E m k' x' y' ∧
      filtDeg (k' + E.diffDeg m) ≤ filtDeg k + r

/-! ### Differential datum -/

/-- Packages a differential in a spectral sequence with its filtration data.
    This bundles a spectral sequence, a page number `r`, a source bidegree `k`,
    a filtration degree function, and a proof that the differential is essential. -/
structure DifferentialDatum (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- The underlying spectral sequence -/
  E : SpectralSequence C ι
  /-- Page number -/
  r : ℤ
  /-- Source bidegree -/
  k : ι
  /-- Filtration degree function assigning a filtration level to each bidegree -/
  filtDeg : ι → ℤ
  /-- The differential at `(r, k)` is essential (nonzero) -/
  is_essential : IsEssentialAt E r k

/-! ### Crossing predicates (Definition 2.7) -/

/-- **Definition 2.7(1)**: The differential `d_r` at `(k, s)` has a **crossing
    hitting filtration `p`**.

    There exists another element at filtration `s + a` (with `a > 0`) whose
    essential differential `d_m` has target at filtration `p = s + a + m`,
    and `p ≤ s + r` (target filtration is at most the original target's). -/
def HasCrossingAt (dd : DifferentialDatum C ι) (p : ℤ) : Prop :=
  let s := dd.filtDeg dd.k
  ∃ (a : ℤ) (_ : 0 < a) (m : ℤ) (k' : ι),
    dd.filtDeg k' = s + a ∧
    IsEssentialAt dd.E m k' ∧
    p = s + a + m ∧
    s + a + m ≤ s + dd.r

/-- **Definition 2.7(2)**: The differential `d_r` at `(k, s)` has **no crossing
    hitting the range Fil ≥ p**.

    There does NOT exist another element at filtration `s + a` (with `a > 0`)
    whose essential differential `d_m` has target filtration in `[p, s + r]`. -/
def NoCrossingRange (dd : DifferentialDatum C ι) (p : ℤ) : Prop :=
  ¬ ∃ (a : ℤ) (_ : 0 < a) (m : ℤ) (k' : ι),
    dd.filtDeg k' = dd.filtDeg dd.k + a ∧
    IsEssentialAt dd.E m k' ∧
    p ≤ dd.filtDeg dd.k + a + m ∧
    dd.filtDeg dd.k + a + m ≤ dd.filtDeg dd.k + dd.r

/-- **Definition 2.7(3)**: The differential `d_r` at `(k, s)` has **no crossing**.

    Equivalent to: no crossing hitting the range `Fil ≥ s + 1`. -/
def NoCrossing (dd : DifferentialDatum C ι) : Prop :=
  NoCrossingRange dd (dd.filtDeg dd.k + 1)

/-! ### SpectralSequence-based constructors -/

/-- Construct a `DifferentialDatum` directly from a spectral sequence, a page `r`,
    a source bidegree `k`, a filtration degree function, and an essentiality proof. -/
def DifferentialDatum.ofSpectralSequence
    (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    (filtDeg : ι → ℤ) (hess : IsEssentialAt E r k) :
    DifferentialDatum C ι :=
  { E := E, r := r, k := k, filtDeg := filtDeg, is_essential := hess }

/-! ### Crossing composed with convergence -/

/-- Crossing predicate relativised to a convergent spectral sequence.
    Given a convergence `conv : Convergence E A F`, this wraps `HasCrossingAt`
    so that the caller does not need to manually extract the filtration degree. -/
def HasCrossingAt_conv {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (_conv : Convergence E A F) (dd : DifferentialDatum C ω) (p : ℤ) : Prop :=
  HasCrossingAt dd p

end KIPBase.SpectralSequence
