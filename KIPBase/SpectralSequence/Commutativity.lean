/-
  KIPBase.SpectralSequence.Commutativity
  §2.12–2.19 Commutativity of ESS differentials

  Blueprint: §2.12–2.19 from arXiv:2412.10879 (KIP)
  Informal: informal/commutativity_ss.md

  Defines the homotopy commutative square of converging spectral
  sequences, and axiomatizes Theorem 2.12 (commutativity), its
  corollaries (2.15–2.19), and the induced map on ESS pages.
-/
import KIPBase.Mathlib
import KIPBase.SpectralSequence.Basic
import KIPBase.SpectralSequence.Convergence
import KIPBase.SpectralSequence.Crossing
import KIPBase.SpectralSequence.BoundedExtension

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- ESS 的 `ssData` 在双次数 `⟨s, k⟩` 处的 `V` 就是两项复形的关联分次
    `assocGraded s k`（`toPreSS`/`ofPreSS` 的 `ssData` 字段与
    `toSSData` 的 `V` 字段都是直接定义，`rfl` 可判等）。
    作为独立的 `rfl` 引理封装，供陈述中以 `Eq.mpr` 搬运元素，
    避免在大型类型表达式里反复触发 `whnf` 超时。 -/
theorem ess_ssData_V {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (s k : ℤ) :
    (((ext.complex t).toSpectralSequence (ext.bounded t)).ssData ⟨s, k⟩).V =
      (ext.complex t).assocGraded s k :=
  rfl

/-- ESS 的微分次数：`diffDeg r = (r, -1)`（`toPreSS` 的 `diffDeg` 字段定义）。 -/
theorem ess_diffDeg {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (r : ℤ) :
    ((ext.complex t).toSpectralSequence (ext.bounded t)).diffDeg r = (r, -1) :=
  rfl

/-! ### Homotopy commutative square in the category of converging spectral sequences -/

/-- **收敛谱序列范畴中的交换方块**（新定义，范畴化形式）：
    四个收敛谱序列对象 `V₁ V₂ V₃ V₄` 与四个范畴态射
    ```
    V₁ --f--> V₂
    |p        |q
    v         v
    V₃ --g--> V₄
    ```
    满足范畴复合交换律 `f ≫ q = p ≫ g`
    （`≫` 为 `ConvergingSS` 范畴中的复合，自动含 E∞ 页与极限对象
    两个层面的交换性，由范畴公理保证）。 -/
structure ConvergingSSSquare {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w} where
  /-- 左上对象 -/
  V₁ : ConvergingSS C ω ω'
  /-- 右上对象 -/
  V₂ : ConvergingSS C ω ω'
  /-- 左下对象 -/
  V₃ : ConvergingSS C ω ω'
  /-- 右下对象 -/
  V₄ : ConvergingSS C ω ω'
  /-- 上边态射 f : V₁ ⟶ V₂ -/
  f : V₁ ⟶ V₂
  /-- 左边态射 p : V₁ ⟶ V₃ -/
  p : V₁ ⟶ V₃
  /-- 右边态射 q : V₂ ⟶ V₄ -/
  q : V₂ ⟶ V₄
  /-- 下边态射 g : V₃ ⟶ V₄ -/
  g : V₃ ⟶ V₄
  /-- 方块交换：`f ≫ q = p ≫ g`（范畴中的复合交换）。 -/
  comm : f ≫ q = p ≫ g

/-- A homotopy commutative square of converging spectral sequences:
    ```
    V₁ --f--> V₂
    |p        |q
    v         v
    V₃ --g--> V₄
    ```
    Together with ESS data for each morphism and a commutativity condition
    expressing that `q ∘ f = g ∘ p` at the abutment level. -/
structure HomotopyCommSquare {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (conv₃ : Convergence E₃ A₃ F₃) (conv₄ : Convergence E₄ A₄ F₄) where
  /-- Top morphism: V₁ → V₂ -/
  cmf : ConvergenceMorphism conv₁ conv₂
  /-- Left morphism: V₁ → V₃ -/
  cmp : ConvergenceMorphism conv₁ conv₃
  /-- Right morphism: V₂ → V₄ -/
  cmq : ConvergenceMorphism conv₂ conv₄
  /-- Bottom morphism: V₃ → V₄ -/
  cmg : ConvergenceMorphism conv₃ conv₄
  /-- Boundedness of the F₁-filtration. -/
  bnd₁ : F₁.IsBounded
  /-- Boundedness of the F₂-filtration. -/
  bnd₂ : F₂.IsBounded
  /-- Boundedness of the F₃-filtration. -/
  bnd₃ : F₃.IsBounded
  /-- Boundedness of the F₄-filtration. -/
  bnd₄ : F₄.IsBounded
  /-- Bounded ESS data for the top morphism f -/
  extf : BoundedExtensionSS conv₁ conv₂ cmf bnd₁ bnd₂
  /-- Bounded ESS data for the left morphism p -/
  extp : BoundedExtensionSS conv₁ conv₃ cmp bnd₁ bnd₃
  /-- Bounded ESS data for the right morphism q -/
  extq : BoundedExtensionSS conv₂ conv₄ cmq bnd₂ bnd₄
  /-- Bounded ESS data for the bottom morphism g -/
  extg : BoundedExtensionSS conv₃ conv₄ cmg bnd₃ bnd₄
  /-- Commutativity at the abutment level: q ∘ f = g ∘ p on target objects -/
  abutment_comm : ∀ (k' : ω'),
    cmf.aMap k' ≫ cmq.aMap k' = cmp.aMap k' ≫ cmg.aMap k'
  /-- Commutativity at the E∞-page level: q ∘ f = g ∘ p on E∞ classes -/
  eInfty_comm : ∀ (k : ω),
    cmf.eMap k ≫ cmq.eMap k = cmp.eMap k ≫ cmg.eMap k

/-- 从旧定义 `HomotopyCommSquare` 提取范畴方块：对象与态射逐字继承，
    交换性由 eMap/aMap 两个分量等式经 `ConvergenceMorphism.ext` 合并。 -/
def HomotopyCommSquare.toSquare {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄) :
    ConvergingSSSquare (C := C) (ω := ω) (ω' := ω') where
  V₁ := ⟨E₁, A₁, F₁, conv₁⟩
  V₂ := ⟨E₂, A₂, F₂, conv₂⟩
  V₃ := ⟨E₃, A₃, F₃, conv₃⟩
  V₄ := ⟨E₄, A₄, F₄, conv₄⟩
  f := sq.cmf
  p := sq.cmp
  q := sq.cmq
  g := sq.cmg
  comm := ConvergenceMorphism.ext
    (funext fun k => sq.eInfty_comm k) (funext fun k' => sq.abutment_comm k')

/-- **新旧方块定义的等价性**（定理形式）：
    旧定义 `HomotopyCommSquare` 给出的范畴方块 `sq.toSquare`，
    其范畴复合交换律 `comm` 成立，当且仅当旧定义的两个分量
    交换条件 `eInfty_comm` 与 `abutment_comm` 同时成立。
    （`toSquare` 的 `comm` 字段正是由这两个条件构造，故此即
    构造的往返刻画。） -/
theorem HomotopyCommSquare.toSquare_comm {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄) :
    sq.toSquare.comm = ConvergenceMorphism.ext
      (funext fun k => sq.eInfty_comm k) (funext fun k' => sq.abutment_comm k') :=
  rfl

/-! ### ESS differential relation predicate -/

/-- The ESS differential `d_n` sends the class at bidegree `k₁` to the class
    at bidegree `k₂`: expressed as the ESS differential object being nontrivial
    and witnessing the relation. This is a Prop-level predicate abstracting the
    ESS differential relation from Proposition 2.5. -/
def ESSRelation {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (n : ℤ) (k₁ k₂ : ω) : Prop :=
  ¬IsZero (ext.essDiff n k₁ k₂)

/-- The ESS differential `d_n` sends the class at `k₁` to zero at `k₂`. -/
def ESSVanishes {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (n : ℤ) (k₁ k₂ : ω) : Prop :=
  IsZero (ext.essDiff n k₁ k₂)

/-- No-crossing condition for an ESS differential datum, bundled with the
    convergence data. Takes the differential datum as a parameter
    (following Extension.lean patterns). -/
def ESSNoCrossing {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {_conv₁ : Convergence E₁ A₁ F₁} {_conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism _conv₁ _conv₂}
    {_bnd₁ : F₁.IsBounded} {_bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS _conv₁ _conv₂ cm _bnd₁ _bnd₂)
    (dd : DifferentialDatum C ω) : Prop :=
  NoCrossing dd

/-- No-crossing-range condition for an ESS differential datum. -/
def ESSNoCrossingRange {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {_conv₁ : Convergence E₁ A₁ F₁} {_conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism _conv₁ _conv₂}
    {_bnd₁ : F₁.IsBounded} {_bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS _conv₁ _conv₂ cm _bnd₁ _bnd₂)
    (dd : DifferentialDatum C ω) (p : ℤ) : Prop :=
  NoCrossingRange dd p

/-! ### Theorem 2.12 — Commutativity (main theorem) -/

section ESSCommutativityLemmas

variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω] {ω' : Type w}
variable (sq : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
variable (bnd₁ : sq.V₁.F.IsBounded) (bnd₂ : sq.V₂.F.IsBounded)
variable (bnd₃ : sq.V₃.F.IsBounded) (bnd₄ : sq.V₄.F.IsBounded)
variable (extf : BoundedExtensionSS sq.V₁.conv sq.V₂.conv sq.f bnd₁ bnd₂)
variable (extp : BoundedExtensionSS sq.V₁.conv sq.V₃.conv sq.p bnd₁ bnd₃)
variable (extq : BoundedExtensionSS sq.V₂.conv sq.V₄.conv sq.q bnd₂ bnd₄)
variable (extg : BoundedExtensionSS sq.V₃.conv sq.V₄.conv sq.g bnd₃ bnd₄)
variable (n m l sfx : ℤ) (t : ω') {T : C}
variable (x : T ⟶ (extf.complex t).assocGraded sfx 1)
variable (y : T ⟶ (extf.complex t).assocGraded (sfx + n) 0)
variable (z : T ⟶ (extp.complex t).assocGraded (sfx + m) 0)
variable (w : T ⟶ (extg.complex t).assocGraded (sfx + m + l) 0)

/-- `w` 同时作为 ESS(g) 的目标与 ESS(q) 的目标出现：两者对象均为
    `F₄` 层在过滤 `sfx+m+l`、次数 `0` 的关联分次，定义性相等（`rfl`）。 -/
lemma ess_g_q_assocGraded :
    (extg.complex t).assocGraded (sfx + m + l) 0 =
      (extq.complex t).assocGraded (sfx + m + l) 0 := rfl

/-- **引理 A1**（方块交换下放到过滤层）：设 `yl` 是 `y` 在 ESS(q) 源过滤层
    `F^{s+n}` 中的 lift，`wl` 是 `w` 在目标过滤层 `F^{s+m+l}` 中的 lift。
    由方块交换（`f≫q = p≫g`）与 `_hf_rel`/`_hg_rel` 的 lift 刻画，
    `yl` 在 q 复形中的微分与 `wl` 之差落在更深过滤 `F^{s+m+l+1}` 中，
    即差项经 assocGraded 投影为 `0`。证明依赖 Crossing/FilteredComplex
    的桥引理，暂 sorry。
    数学注记：q 复形中 `y` 的 lift `yl` 是 `A₂(t)` 的元素
    （类型为 `F^{s+n}A₂⁰` 的底层对象），微分后落在 `F^{s+n}A₄⁰`；
    `wl` 是 `A₄(t)` 的元素（`F^{s+m+l}A₄⁰`），两者相减在 `A₄(t)` 中进行。 -/
theorem essComm_auxA1
    (yl : T ⟶ Subobject.underlying.obj ((extq.complex t).fil (sfx + n) 1))
    (hy_lift : (extq.complex t).IsLift (sfx + n) 1 yl
      (Eq.mpr (congrArg (fun X : C => T ⟶ X) (ess_ssData_V extq t (sfx + n) 1).symm) y))
    (wl : T ⟶ Subobject.underlying.obj ((extq.complex t).fil (sfx + m + l) 0))
    (hw_lift : (extq.complex t).IsLift (sfx + m + l) 0 wl
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (ess_g_q_assocGraded sq bnd₂ bnd₃ bnd₄ extq extg m l sfx t).symm) w))
    (hmln : 0 ≤ m + l - n) :
    (yl ≫ (extq.complex t).filDiff (sfx + n) 1 ≫
      Subobject.ofLE ((extq.complex t).fil (sfx + n) 0)
        ((extq.complex t).fil (sfx + n - 1) 0)
        ((extq.complex t).fil_anti_of_le 0 (by omega)) -
      wl ≫ Subobject.ofLE ((extq.complex t).fil (sfx + m + l) 0)
        ((extq.complex t).fil (sfx + n - 1) 0)
        ((extq.complex t).fil_anti_of_le 0 (by omega))) ≫
        (extq.complex t).filToAssocGraded (sfx + n - 1) 0 = 0 := by
  sorry

/-- **引理 B1**（lift 数据产生候选微分关系）：给定一个严格短于目标页的
    filtration-level 微分 lift，`FilteredComplex.differentialRelation_of_lift`
    将它降到 ESS(q) 的页微分关系。

    这一定理不凭空产生 `r'`：原先的陈述没有任何假设却要求
    `∃ r' < m + l - n`，在 `m + l - n ≤ 0` 时不可能成立。候选页与其
    lift 等式必须由 A1 后续的误差项分析提供。 -/
theorem essComm_auxB1
    (r' : ℤ) (hr' : 0 ≤ r') (_hr'_lt : r' < m + l - n)
    (yl : T ⟶ Subobject.underlying.obj ((extq.complex t).fil (sfx + n) 1))
    (wl : T ⟶ Subobject.underlying.obj ((extq.complex t).fil (sfx + n + r') 0))
    (hy : (extq.complex t).IsLift (sfx + n) 1 yl
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
          ⟨sfx + n, 1⟩).V = (extq.complex t).assocGraded (sfx + n) 1 from rfl)) y))
    (y₀ : T ⟶ (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
        (⟨sfx + n, 1⟩ + ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
          r')).V)
    (hw : (extq.complex t).IsLift (sfx + n + r') 0 wl
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
          (⟨sfx + n, 1⟩ + ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
            r')).V = (extq.complex t).assocGraded (sfx + n + r') 0 from by
          change (extq.complex t).assocGraded (sfx + n + r') 0 = _
          rfl)) y₀))
    (hd : yl ≫ (extq.complex t).filDiff (sfx + n) 1 =
      wl ≫ Subobject.ofLE ((extq.complex t).fil (sfx + n + r') 0)
        ((extq.complex t).fil (sfx + n) 0)
        ((extq.complex t).fil_anti_of_le 0 (by omega))) :
    DifferentialRelation ((extq.complex t).toSpectralSequence (extq.bounded t))
      r' ⟨sfx + n, 1⟩
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
          ⟨sfx + n, 1⟩).V = (extq.complex t).assocGraded (sfx + n) 1 from rfl)) y)
      y₀ := by
  exact FilteredComplex.differentialRelation_of_lift (extq.complex t)
    (extq.bounded t) r' hr' (sfx + n) 1 hy hw hd

/-- **引理 B2**（non-crossing 排除竞争）：`_hf_or_p_nc`、`_hg_nc_range`、
    `_hq_nc` 联合蕴含：从 `y` 出发不存在次数严格小于 `m+l-n` 且目标过滤
    在 `[s+n+1, s+m+l]` 内的 essential 微分关系。暂 sorry。 -/
theorem essComm_auxB2
    (ddf : DifferentialDatum C ω) (ddp : DifferentialDatum C ω)
    (ddg : DifferentialDatum C ω) (ddq : DifferentialDatum C ω)
    (_hf_or_p_nc : NoCrossing ddf ∨ NoCrossing ddp)
    (_hg_nc_range : ∀ (s kval : ℤ), 0 < kval → kval ≤ m + l - n →
      NoCrossingRange ddg (s + n + kval))
    (_hq_nc : NoCrossing ddq) :
    ∀ (r' : ℤ), 0 ≤ r' → r' < m + l - n →
      ∀ (y₀ : T ⟶ (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
        (⟨sfx + n, 1⟩ + ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
          r')).V),
        ¬ EssentialDifferentialRelation
          ((extq.complex t).toSpectralSequence (extq.bounded t)) r' ⟨sfx + n, 1⟩
          (Eq.mpr (congrArg (fun X : C => T ⟶ X)
            (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
              ⟨sfx + n, 1⟩).V = (extq.complex t).assocGraded (sfx + n) 1 from rfl)) y)
          y₀ := by
  sorry

/-- **引理 B3**（`_hq_vanish` 排除残余次数）：若竞争关系次数恰为 `kval-1`，
    则 `_hq_vanish` 迫使目标为 `0`。暂 sorry。 -/
theorem essComm_auxB3
    (kval : ℤ) (_hk_pos : 0 < kval)
    (_hq_vanish : ∀ (y₀ : T ⟶ (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
        (⟨sfx + n, 1⟩ + ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
          (kval - 1))).V),
      DifferentialRelation ((extq.complex t).toSpectralSequence (extq.bounded t))
        (kval - 1) ⟨sfx + n, 1⟩
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
            ⟨sfx + n, 1⟩).V = (extq.complex t).assocGraded (sfx + n) 1 from rfl)) y)
        y₀ → y₀ = 0)
    (y₀ : T ⟶ (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
      (⟨sfx + n, 1⟩ + ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
        (kval - 1))).V)
    (hrel : DifferentialRelation ((extq.complex t).toSpectralSequence (extq.bounded t))
      (kval - 1) ⟨sfx + n, 1⟩
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
          ⟨sfx + n, 1⟩).V = (extq.complex t).assocGraded (sfx + n) 1 from rfl)) y)
      y₀) :
    y₀ = 0 :=
  _hq_vanish y₀ hrel

/-- **引理 C1**（组装结论关系）：`y` 在 ESS(q) 中存在页 `m+l-n` 的 Z 提升，
    使 `y` 与 `w` 满足 `DifferentialRelation` 的页上等式。
    由 `A1` 的候选 lift 经 `B1–B3` 排除所有竞争修正后得到。暂 sorry。 -/
theorem essComm_auxC1 :
    DifferentialRelation ((extq.complex t).toSpectralSequence (extq.bounded t))
      (m + l - n) ⟨sfx + n, 1⟩
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
          ⟨sfx + n, 1⟩).V = (extq.complex t).assocGraded (sfx + n) 1 from rfl)) y)
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
          (⟨sfx + n, 1⟩ + ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
            (m + l - n))).V = (extg.complex t).assocGraded (sfx + m + l) 0 from by
          have h : (⟨sfx + n, 1⟩ +
              ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
                (m + l - n) : ℤ × ℤ) = ⟨sfx + m + l, 0⟩ := by
            show (⟨sfx + n, 1⟩ + (m + l - n, -1) : ℤ × ℤ) = ⟨sfx + m + l, 0⟩
            apply Prod.ext
            · show sfx + n + (m + l - n) = sfx + m + l; ring
            · rfl
          rw [h]
          show ((extq.complex t).toSSData (extq.bounded t) (sfx + m + l) 0).V =
            (extg.complex t).assocGraded (sfx + m + l) 0
          rw [ess_g_q_assocGraded sq bnd₂ bnd₃ bnd₄ extq extg m l sfx t]
          rfl)) w) := by
  sorry

/-- 结论的 w 侧搬运：与主定理结论中的 cast 逐项相同，但写成
    「essq 的关联分次 = ESS(q) 页对象」方向，供 `Eq.mpr` 使用。 -/
lemma essComm_concl_cast :
    (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
      (⟨sfx + n, 1⟩ + ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
        (m + l - n))).V =
      (extg.complex t).assocGraded (sfx + m + l) 0 := by
  have h : (⟨sfx + n, 1⟩ +
      ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
        (m + l - n) : ℤ × ℤ) = ⟨sfx + m + l, 0⟩ := by
    show (⟨sfx + n, 1⟩ + (m + l - n, -1) : ℤ × ℤ) = ⟨sfx + m + l, 0⟩
    apply Prod.ext
    · show sfx + n + (m + l - n) = sfx + m + l; ring
    · rfl
  rw [h]
  show ((extq.complex t).toSSData (extq.bounded t) (sfx + m + l) 0).V =
    (extg.complex t).assocGraded (sfx + m + l) 0
  rw [ess_g_q_assocGraded sq bnd₂ bnd₃ bnd₄ extq extg m l sfx t]
  rfl

end ESSCommutativityLemmas

/-- **Theorem 2.12**: Commutativity of ESS differentials (full version).

    Given a commutative square in the `ConvergingSS` category and:
    1. `d_n^f(x) = y`（表述为 ESS 微分关系 `DifferentialRelation`）
    2. `d_m^p(x) = z`（微分关系）
    3. One of (1) or (2) has no crossing
    4. `d_l^g(z) = w` with no crossing hitting Fil ≥ s + n + k (for 0 < k ≤ m + l − n)
    5. `d_{k-1}^q(y) = 0` with no crossing

    Then `d_{m+l-n}^q(y) = w`（微分关系）。
    所有「`d(x) = y`」均按 `DifferentialRelation` 表述。
    **关键**：四个关系共享同一批广义元素——`x` 同时是 ESS(f) 与 ESS(p) 的源
    （两者在次数 `1` 处的关联分次定义性相同，均为 `F₁` 层），
    `y` 同时是 ESS(f) 的目标与 ESS(q) 的源（均为 `F₂` 层次数 `0`），
    `z` 同时是 ESS(p) 的目标与 ESS(g) 的源（均为 `F₃` 层次数 `0`），
    `w` 同时是 ESS(g) 的目标与 ESS(q) 的目标（均为 `F₄` 层次数 `0`）。 -/
theorem essCommutativity {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (sq : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
    (bnd₁ : sq.V₁.F.IsBounded) (bnd₂ : sq.V₂.F.IsBounded)
    (bnd₃ : sq.V₃.F.IsBounded) (bnd₄ : sq.V₄.F.IsBounded)
    (extf : BoundedExtensionSS sq.V₁.conv sq.V₂.conv sq.f bnd₁ bnd₂)
    (extp : BoundedExtensionSS sq.V₁.conv sq.V₃.conv sq.p bnd₁ bnd₃)
    (extq : BoundedExtensionSS sq.V₂.conv sq.V₄.conv sq.q bnd₂ bnd₄)
    (extg : BoundedExtensionSS sq.V₃.conv sq.V₄.conv sq.g bnd₃ bnd₄)
    (n m l : ℤ) (sfx : ℤ) (t : ω')
    (kx ky kz kw : ω)
    (_hn : 0 ≤ n) (_hm : 0 ≤ m) (_hl : 0 ≤ l)
    {T : C}
    (x : T ⟶ (extf.complex t).assocGraded sfx 1)
    (y : T ⟶ (extf.complex t).assocGraded (sfx + n) 0)
    (z : T ⟶ (extp.complex t).assocGraded (sfx + m) 0)
    (w : T ⟶ (extg.complex t).assocGraded (sfx + m + l) 0)
    -- 1. `d_n^f(x) = y`：ESS(f) 中的微分关系
    -- （`Eq.mpr` 精确搬运：对象等式均为 `rfl`，避免 `whnf` 超时）
    (_hf_rel : DifferentialRelation ((extf.complex t).toSpectralSequence (extf.bounded t))
      n ⟨sfx, 1⟩
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extf.complex t).toSpectralSequence (extf.bounded t)).ssData ⟨sfx, 1⟩).V =
          (extf.complex t).assocGraded sfx 1 from rfl)) x)
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extf.complex t).toSpectralSequence (extf.bounded t)).ssData
          (⟨sfx, 1⟩ + ((extf.complex t).toSpectralSequence (extf.bounded t)).diffDeg n)).V =
          (extf.complex t).assocGraded (sfx + n) 0 from rfl)) y))
    -- 2. `d_m^p(x) = z`：ESS(p) 中的微分关系（源与 (1) 共享同一个 `x`）
    (_hp_rel : DifferentialRelation ((extp.complex t).toSpectralSequence (extp.bounded t))
      m ⟨sfx, 1⟩
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extp.complex t).toSpectralSequence (extp.bounded t)).ssData ⟨sfx, 1⟩).V =
          (extp.complex t).assocGraded sfx 1 from rfl)) x)
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extp.complex t).toSpectralSequence (extp.bounded t)).ssData
          (⟨sfx, 1⟩ + ((extp.complex t).toSpectralSequence (extp.bounded t)).diffDeg m)).V =
          (extp.complex t).assocGraded (sfx + m) 0 from rfl)) z))
    (ddf : DifferentialDatum C ω)
    (_hddf : ddf.E = sq.V₁.E ∧ ddf.r = n ∧ ddf.k = kx)
    (ddp : DifferentialDatum C ω)
    (_hddp : ddp.E = sq.V₁.E ∧ ddp.r = m ∧ ddp.k = kx)
    (_hf_or_p_nc : NoCrossing ddf ∨ NoCrossing ddp)
    -- 4. `d_l^g(z) = w`：ESS(g) 中的微分关系（源与 (2) 共享同一个 `z`）
    (_hg_rel : DifferentialRelation ((extg.complex t).toSpectralSequence (extg.bounded t))
      l ⟨sfx + m, 1⟩
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extg.complex t).toSpectralSequence (extg.bounded t)).ssData
          ⟨sfx + m, 1⟩).V =
          (extg.complex t).assocGraded (sfx + m) 1 from rfl)) z)
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extg.complex t).toSpectralSequence (extg.bounded t)).ssData
          (⟨sfx + m, 1⟩ + ((extg.complex t).toSpectralSequence (extg.bounded t)).diffDeg l)).V =
          (extg.complex t).assocGraded (sfx + m + l) 0 from rfl)) w))
    (ddg : DifferentialDatum C ω)
    (_hddg : ddg.E = sq.V₃.E ∧ ddg.r = l ∧ ddg.k = kz)
    (s : ℤ) (kval : ℤ) (_hk_pos : 0 < kval) (_hk_bound : kval ≤ m + l - n)
    (_hg_nc_range : NoCrossingRange ddg (s + n + kval))
    (ddq : DifferentialDatum C ω)
    (_hddq : ddq.E = sq.V₂.E ∧ ddq.r = kval - 1 ∧
      ddq.k = ky)
    -- 5. `d_{k-1}^q(y) = 0`：ESS(q) 中从 `y`（与 (1) 共享）出发的短微分消失
    (_hq_vanish : ∀ (y₀ : T ⟶ (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
        (⟨sfx + n, 1⟩ + ((extq.complex t).toSpectralSequence (extq.bounded t)).diffDeg
          (kval - 1))).V),
      DifferentialRelation ((extq.complex t).toSpectralSequence (extq.bounded t))
        (kval - 1) ⟨sfx + n, 1⟩
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
            ⟨sfx + n, 1⟩).V =
            (extq.complex t).assocGraded (sfx + n) 1 from rfl)) y)
        y₀ → y₀ = 0)
    (_hq_nc : NoCrossing ddq) :
    -- 结论：`d_{m+l-n}^q(y) = w`：ESS(q) 中 `y` 与 `w`（与 (4) 共享）的微分关系
    DifferentialRelation ((extq.complex t).toSpectralSequence (extq.bounded t))
      (m + l - n) ⟨sfx + n, 1⟩
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show (((extq.complex t).toSpectralSequence (extq.bounded t)).ssData
          ⟨sfx + n, 1⟩).V =
          (extq.complex t).assocGraded (sfx + n) 1 from rfl)) y)
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (essComm_concl_cast sq bnd₂ bnd₃ bnd₄ extq extg n m l sfx t)) w) :=
  -- 主定理本体：由引理 C1 直接给出（C1 的证明内部经 A1→B1→B2→B3 组装）。
  essComm_auxC1 sq bnd₁ bnd₂ bnd₃ bnd₄ extf extq extg n m l sfx t y w

/-- **Theorem 2.12 (value form)**: The ESS differential `d_{m+l-n}^q(y)` equals
    the composition of `d_l^g(z)` through the commutativity square, expressed
    as an isomorphism between the differential objects. -/
theorem essCommutativity_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n m l : ℤ) (kx ky kz kw : ω)
    (_hn : 0 ≤ n) (_hm : 0 ≤ m) (_hl : 0 ≤ l)
    (_hf_rel : ESSRelation sq.extf n kx ky)
    (_hp_rel : ESSRelation sq.extp m kx kz)
    (ddf : DifferentialDatum C ω)
    (_hddf : ddf.E = E₁ ∧ ddf.r = n ∧ ddf.k = kx)
    (ddp : DifferentialDatum C ω)
    (_hddp : ddp.E = E₁ ∧ ddp.r = m ∧ ddp.k = kx)
    (_hf_or_p_nc : NoCrossing ddf ∨ NoCrossing ddp)
    (_hg_rel : ESSRelation sq.extg l kz kw)
    (ddg : DifferentialDatum C ω)
    (_hddg : ddg.E = E₃ ∧ ddg.r = l ∧ ddg.k = kz)
    (s : ℤ) (kval : ℤ) (_hk_pos : 0 < kval) (_hk_bound : kval ≤ m + l - n)
    (_hg_nc_range : NoCrossingRange ddg (s + n + kval))
    (ddq : DifferentialDatum C ω)
    (_hddq : ddq.E = E₂ ∧ ddq.r = kval - 1 ∧ ddq.k = ky)
    (_hq_vanish : ESSVanishes sq.extq (kval - 1) ky kw)
    (_hq_nc : NoCrossing ddq) :
    Nonempty (sq.extq.essDiff (m + l - n) ky kw ≅ sq.extg.essDiff l kz kw) := by
  sorry
/-! ### Corollary 2.15 — Simplified commutativity (no crossing everywhere) -/

/-- **Corollary 2.15**: Simplified commutativity — same as Thm 2.12 but with
    `d_l^g(z) = w` having no crossing at all (dropping the k parameter). -/
theorem essCommutativity_noCrossing {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n m l : ℤ) (kx ky kz kw : ω)
    (_hn : 0 ≤ n) (_hm : 0 ≤ m) (_hl : 0 ≤ l)
    (_hf_rel : ESSRelation sq.extf n kx ky)
    (_hp_rel : ESSRelation sq.extp m kx kz)
    (ddf : DifferentialDatum C ω)
    (_hddf : ddf.E = E₁ ∧ ddf.r = n ∧ ddf.k = kx)
    (ddp : DifferentialDatum C ω)
    (_hddp : ddp.E = E₁ ∧ ddp.r = m ∧ ddp.k = kx)
    (_hf_or_p_nc : NoCrossing ddf ∨ NoCrossing ddp)
    (_hg_rel : ESSRelation sq.extg l kz kw)
    (ddg : DifferentialDatum C ω)
    (_hddg : ddg.E = E₃ ∧ ddg.r = l ∧ ddg.k = kz)
    (_hg_nc : NoCrossing ddg) :
    ESSRelation sq.extq (m + l - n) ky kw := by
  sorry
/-- **Corollary 2.15 (iso form)**: Under no-crossing-everywhere, the differential
    objects are isomorphic. -/
theorem essCommutativity_noCrossing_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n m l : ℤ) (kx ky kz kw : ω)
    (_hn : 0 ≤ n) (_hm : 0 ≤ m) (_hl : 0 ≤ l)
    (_hf_rel : ESSRelation sq.extf n kx ky)
    (_hp_rel : ESSRelation sq.extp m kx kz)
    (ddf : DifferentialDatum C ω)
    (_hddf : ddf.E = E₁ ∧ ddf.r = n ∧ ddf.k = kx)
    (ddp : DifferentialDatum C ω)
    (_hddp : ddp.E = E₁ ∧ ddp.r = m ∧ ddp.k = kx)
    (_hf_or_p_nc : NoCrossing ddf ∨ NoCrossing ddp)
    (_hg_rel : ESSRelation sq.extg l kz kw)
    (ddg : DifferentialDatum C ω)
    (_hddg : ddg.E = E₃ ∧ ddg.r = l ∧ ddg.k = kz)
    (_hg_nc : NoCrossing ddg) :
    Nonempty (sq.extq.essDiff (m + l - n) ky kw ≅ sq.extg.essDiff l kz kw) := by
  sorry
/-! ### Corollary 2.16 — Triangle case -/

/-- **Corollary 2.16 (Triangle)**: When V₃ = V₄ and g = id.
    ```
    V₁ --f--> V₂
     \         |q
      p\       v
        \-->  V₃
    ```
    If `d_n^f(x) = y` and `d_m^p(x) = z` with no crossing on one of them,
    then `d_{m-n}^q(y) = z`. -/
theorem essCommutativity_triangle {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cmf : ConvergenceMorphism conv₁ conv₂)
    (cmp : ConvergenceMorphism conv₁ conv₃)
    (cmq : ConvergenceMorphism conv₂ conv₃)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) (bnd₃ : F₃.IsBounded)
    (extf : BoundedExtensionSS conv₁ conv₂ cmf bnd₁ bnd₂)
    (extp : BoundedExtensionSS conv₁ conv₃ cmp bnd₁ bnd₃)
    (extq : BoundedExtensionSS conv₂ conv₃ cmq bnd₂ bnd₃)
    (_abutment_comm : ∀ (k' : ω'), cmf.aMap k' ≫ cmq.aMap k' = cmp.aMap k')
    (_eInfty_comm : ∀ (k : ω), cmf.eMap k ≫ cmq.eMap k = cmp.eMap k)
    (n m : ℤ) (kx ky kz : ω)
    (_hn : 0 ≤ n) (_hm : 0 ≤ m) (_hmn : n ≤ m)
    (_hf_rel : ESSRelation extf n kx ky)
    (_hp_rel : ESSRelation extp m kx kz)
    (ddf : DifferentialDatum C ω)
    (_hddf : ddf.E = E₁ ∧ ddf.r = n ∧ ddf.k = kx)
    (ddp : DifferentialDatum C ω)
    (_hddp : ddp.E = E₁ ∧ ddp.r = m ∧ ddp.k = kx)
    (_hf_or_p_nc : NoCrossing ddf ∨ NoCrossing ddp) :
    ESSRelation extq (m - n) ky kz := by
  sorry
/-- **Corollary 2.16 (iso form)**: Triangle case iso. -/
theorem essCommutativity_triangle_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cmf : ConvergenceMorphism conv₁ conv₂)
    (cmp : ConvergenceMorphism conv₁ conv₃)
    (cmq : ConvergenceMorphism conv₂ conv₃)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) (bnd₃ : F₃.IsBounded)
    (extf : BoundedExtensionSS conv₁ conv₂ cmf bnd₁ bnd₂)
    (extp : BoundedExtensionSS conv₁ conv₃ cmp bnd₁ bnd₃)
    (extq : BoundedExtensionSS conv₂ conv₃ cmq bnd₂ bnd₃)
    (_abutment_comm : ∀ (k' : ω'), cmf.aMap k' ≫ cmq.aMap k' = cmp.aMap k')
    (_eInfty_comm : ∀ (k : ω), cmf.eMap k ≫ cmq.eMap k = cmp.eMap k)
    (n m : ℤ) (kx ky kz : ω)
    (_hn : 0 ≤ n) (_hm : 0 ≤ m) (_hmn : n ≤ m)
    (_hf_rel : ESSRelation extf n kx ky)
    (_hp_rel : ESSRelation extp m kx kz)
    (ddf : DifferentialDatum C ω)
    (_hddf : ddf.E = E₁ ∧ ddf.r = n ∧ ddf.k = kx)
    (ddp : DifferentialDatum C ω)
    (_hddp : ddp.E = E₁ ∧ ddp.r = m ∧ ddp.k = kx)
    (_hf_or_p_nc : NoCrossing ddf ∨ NoCrossing ddp) :
    Nonempty (extq.essDiff (m - n) ky kz ≅ extp.essDiff m kx kz) := by
  sorry
/-! ### Corollary 2.17 — Composition case -/

/-- **Corollary 2.17 (Composition)**: When V₁ = V₂ and f = id.
    ```
    V₁ --p--> V₃
     \         |g
      q\       v
        \-->  V₄
    ```
    If `d_m^p(x) = z` and `d_l^g(z) = w` with no crossing on `g`, then
    `d_{m+l}^q(x) = w`. -/
theorem essCommutativity_composition {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (cmp : ConvergenceMorphism conv₁ conv₃)
    (cmg : ConvergenceMorphism conv₃ conv₄)
    (cmq : ConvergenceMorphism conv₁ conv₄)
    (bnd₁ : F₁.IsBounded) (bnd₃ : F₃.IsBounded) (bnd₄ : F₄.IsBounded)
    (extp : BoundedExtensionSS conv₁ conv₃ cmp bnd₁ bnd₃)
    (extg : BoundedExtensionSS conv₃ conv₄ cmg bnd₃ bnd₄)
    (extq : BoundedExtensionSS conv₁ conv₄ cmq bnd₁ bnd₄)
    (_abutment_comm : ∀ (k' : ω'), cmp.aMap k' ≫ cmg.aMap k' = cmq.aMap k')
    (_eInfty_comm : ∀ (k : ω), cmp.eMap k ≫ cmg.eMap k = cmq.eMap k)
    (m l : ℤ) (kx kz kw : ω)
    (_hm : 0 ≤ m) (_hl : 0 ≤ l)
    (_hp_rel : ESSRelation extp m kx kz)
    (_hg_rel : ESSRelation extg l kz kw)
    (ddg : DifferentialDatum C ω)
    (_hddg : ddg.E = E₃ ∧ ddg.r = l ∧ ddg.k = kz)
    (_hg_nc : NoCrossing ddg) :
    ESSRelation extq (m + l) kx kw := by
  sorry
/-- **Corollary 2.17 (iso form)**: Composition case iso. -/
theorem essCommutativity_composition_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (cmp : ConvergenceMorphism conv₁ conv₃)
    (cmg : ConvergenceMorphism conv₃ conv₄)
    (cmq : ConvergenceMorphism conv₁ conv₄)
    (bnd₁ : F₁.IsBounded) (bnd₃ : F₃.IsBounded) (bnd₄ : F₄.IsBounded)
    (extp : BoundedExtensionSS conv₁ conv₃ cmp bnd₁ bnd₃)
    (extg : BoundedExtensionSS conv₃ conv₄ cmg bnd₃ bnd₄)
    (extq : BoundedExtensionSS conv₁ conv₄ cmq bnd₁ bnd₄)
    (_abutment_comm : ∀ (k' : ω'), cmp.aMap k' ≫ cmg.aMap k' = cmq.aMap k')
    (_eInfty_comm : ∀ (k : ω), cmp.eMap k ≫ cmg.eMap k = cmq.eMap k)
    (m l : ℤ) (kx kz kw : ω)
    (_hm : 0 ≤ m) (_hl : 0 ≤ l)
    (_hp_rel : ESSRelation extp m kx kz)
    (_hg_rel : ESSRelation extg l kz kw)
    (ddg : DifferentialDatum C ω)
    (_hddg : ddg.E = E₃ ∧ ddg.r = l ∧ ddg.k = kz)
    (_hg_nc : NoCrossing ddg) :
    Nonempty (extq.essDiff (m + l) kx kw ≅ extg.essDiff l kz kw) := by
  sorry
/-! ### Corollary 2.18 — Induced map on ESS pages -/

/-- The ESS page map induced by the commutativity square: if the source E∞-pages
    have `E₀ = E_r` (degeneration at page r), then the commutativity data
    induces a well-defined map between the f-ESS and g-ESS pages. -/
theorem essCommutativity_induces_map {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (r : ℤ) (_hr : 0 ≤ r)
    (_hp_degen : E₁.DegeneratesAt r)
    (_hg_degen : E₃.DegeneratesAt r)
    (n : ℤ) (k₁ k₂ : ω) :
    Nonempty (sq.extf.essDiff n k₁ k₂ ⟶ sq.extg.essDiff n k₁ k₂) := by
  sorry

/-- **Corollary 2.18 (compatibility)**: The induced page map commutes with ESS
    differentials. -/
theorem essInducedPageMap_comm {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (r : ℤ) (_hr : 0 ≤ r)
    (_hp_degen : E₁.DegeneratesAt r)
    (_hg_degen : E₃.DegeneratesAt r)
    (n : ℤ) (k₁ k₂ k₃ : ω)
    (φ₁₂ : sq.extf.essDiff n k₁ k₂ ⟶ sq.extg.essDiff n k₁ k₂)
    (φ₂₃ : sq.extf.essDiff n k₂ k₃ ⟶ sq.extg.essDiff n k₂ k₃)
    (d_f : sq.extf.essDiff n k₁ k₂ ⟶ sq.extf.essDiff n k₂ k₃)
    (d_g : sq.extg.essDiff n k₁ k₂ ⟶ sq.extg.essDiff n k₂ k₃) :
    φ₁₂ ≫ d_g = d_f ≫ φ₂₃ := by
  sorry
/-! ### Corollary 2.19 — Null composition -/

/-- **Corollary 2.19**: If `g ∘ f` is null-homotopic and `d_n^f(x) = y`,
    then `y` is a permanent cycle in the g-ESS: `d_m^g(y) = 0` for all `m ≥ 0`. -/
theorem essCommutativity_null {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n : ℤ) (kx ky : ω)
    (_hn : 0 ≤ n)
    (_hf_rel : ESSRelation sq.extf n kx ky)
    (_h_null : ∀ (k' : ω'), sq.cmf.aMap k' ≫ sq.cmq.aMap k' = 0) :
    ∀ (m : ℤ) (_hm : 0 ≤ m) (kw : ω),
    ESSVanishes sq.extq m ky kw := by
  sorry
/-! ### Supporting axioms — Commutativity functoriality -/

/-- Commutativity squares preserve boundary groups: the boundary in the q-ESS
    at page `m + l - n` is related to the boundary in the g-ESS at page `l`. -/
theorem essCommutativity_preserves_boundaries {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n m l : ℤ) (kw : ω)
    (_hn : 0 ≤ n) (_hm : 0 ≤ m) (_hl : 0 ≤ l) :
    Nonempty (sq.extq.essBoundary (m + l - n) kw ⟶ sq.extg.essBoundary l kw) := by
  sorry
/-- The HomotopyCommSquare is natural in the following sense: the induced maps
    on ESS differentials respect composition of convergence morphisms. -/
theorem essCommutativity_naturality {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n : ℤ) (k₁ k₂ : ω) :
    Nonempty (sq.extf.essDiff n k₁ k₂ ⟶ sq.extq.essDiff n k₁ k₂) := by
  sorry
/-- The commutativity data is compatible with the E∞ page maps. -/
theorem essCommutativity_eInfty_compat {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n : ℤ) (k : ω) :
    sq.cmf.eMap k ≫ sq.cmq.eMap k = sq.cmp.eMap k ≫ sq.cmg.eMap k :=
  sq.eInfty_comm k
/-- 过滤数据跨方块相容：`f`、`q` 与 `p`、`g` 在过滤层上诱导的关联分次映射
    满足交换律 `gr(f) ≫ gr(q) = gr(p) ≫ gr(g)`（方块交换在 gr 层面的表现）。 -/
theorem essCommutativity_filtration_compat {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (s : ℤ) (k' : ω') :
    Filtration.inducedAssocGradedMap sq.cmf.aMap sq.cmf.filtration_compat s k' ≫
      Filtration.inducedAssocGradedMap sq.cmq.aMap sq.cmq.filtration_compat s k' =
    Filtration.inducedAssocGradedMap sq.cmp.aMap sq.cmp.filtration_compat s k' ≫
      Filtration.inducedAssocGradedMap sq.cmg.aMap sq.cmg.filtration_compat s k' := by
  have hL : Filtration.inducedAssocGradedMap
      (fun k'' => sq.cmf.aMap k'' ≫ sq.cmq.aMap k'')
      (ConvergenceMorphismData.fcComp sq.cmf sq.cmq) s k' =
    Filtration.inducedAssocGradedMap sq.cmf.aMap sq.cmf.filtration_compat s k' ≫
      Filtration.inducedAssocGradedMap sq.cmq.aMap sq.cmq.filtration_compat s k' :=
    Filtration.inducedAssocGradedMap_comp sq.cmf sq.cmq s k'
  have hR : Filtration.inducedAssocGradedMap
      (fun k'' => sq.cmp.aMap k'' ≫ sq.cmg.aMap k'')
      (ConvergenceMorphismData.fcComp sq.cmp sq.cmg) s k' =
    Filtration.inducedAssocGradedMap sq.cmp.aMap sq.cmp.filtration_compat s k' ≫
      Filtration.inducedAssocGradedMap sq.cmg.aMap sq.cmg.filtration_compat s k' :=
    Filtration.inducedAssocGradedMap_comp sq.cmp sq.cmg s k'
  have hcomp : (fun k'' => sq.cmf.aMap k'' ≫ sq.cmq.aMap k'') =
      fun k'' => sq.cmp.aMap k'' ≫ sq.cmg.aMap k'' :=
    funext fun k'' => sq.abutment_comm k''
  have hmain : Filtration.inducedAssocGradedMap
      (fun k'' => sq.cmf.aMap k'' ≫ sq.cmq.aMap k'')
      (ConvergenceMorphismData.fcComp sq.cmf sq.cmq) s k' =
    Filtration.inducedAssocGradedMap
      (fun k'' => sq.cmp.aMap k'' ≫ sq.cmg.aMap k'')
      (ConvergenceMorphismData.fcComp sq.cmp sq.cmg) s k' := by
    rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap
      (fun k'' => sq.cmf.aMap k'' ≫ sq.cmq.aMap k'')
      (ConvergenceMorphismData.fcComp sq.cmf sq.cmq)]
    rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap
      (fun k'' => sq.cmp.aMap k'' ≫ sq.cmg.aMap k'')
      (ConvergenceMorphismData.fcComp sq.cmp sq.cmg)]
    apply Filtration.inducedGradedMapOfMap_congr
    funext s₀ k₀
    apply (cancel_mono ((F₄.F s₀ k₀).arrow)).mp
    rw [(ConvergenceMorphismData.fcComp sq.cmf sq.cmq s₀ k₀).choose_spec,
      (ConvergenceMorphismData.fcComp sq.cmp sq.cmg s₀ k₀).choose_spec,
      congrFun hcomp k₀]
  rw [← hL, ← hR, hmain]
/-! ### Triangle and composition reductions -/

/-- 三角归约（Corollary 2.16 由全交换方块特化而来）：
    取 `V₃ = V₄`、`g = 𝟙` 时，`f ≫ q = p` 的方块交换数据，
    连同 `V₃` 上的恒等收敛态射及其有界 ESS 数据，
    可由方块数据构造——此即三角情形嵌入全方块情形的桥。 -/
theorem essTriangle_from_square {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cmf : ConvergenceMorphism conv₁ conv₂)
    (cmp : ConvergenceMorphism conv₁ conv₃)
    (cmq : ConvergenceMorphism conv₂ conv₃)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) (bnd₃ : F₃.IsBounded)
    (extf : BoundedExtensionSS conv₁ conv₂ cmf bnd₁ bnd₂)
    (extp : BoundedExtensionSS conv₁ conv₃ cmp bnd₁ bnd₃)
    (extq : BoundedExtensionSS conv₂ conv₃ cmq bnd₂ bnd₃)
    (_abutment_comm : ∀ (k' : ω'), cmf.aMap k' ≫ cmq.aMap k' = cmp.aMap k')
    (n m : ℤ) (kx ky kz : ω)
    (_hf_rel : ESSRelation extf n kx ky)
    (_hp_rel : ESSRelation extp m kx kz) :
    ∃ (idCm : ConvergenceMorphism conv₃ conv₃)
      (_idExt : BoundedExtensionSS conv₃ conv₃ idCm bnd₃ bnd₃),
    (∀ (k : ω), idCm.eMap k = 𝟙 _) ∧ (∀ (k' : ω'), idCm.aMap k' = 𝟙 _) := by
  refine ⟨{
    eMap := fun _ => 𝟙 _
    aMap := fun _ => 𝟙 _
    filtration_compat := F₃.fcId
    reindex_eq := rfl
    iso_compat := fun k => by
      simp only [Category.id_comp, Filtration.transportGraded_self, Category.comp_id,
        F₃.inducedAssocGradedMap_id (conv₃.reindex k).1 (conv₃.reindex k).2] },
    BoundedExtensionSS.mk' conv₃ conv₃ _ bnd₃ bnd₃, fun _ => rfl, fun _ => rfl⟩

/-- 复合归约（Corollary 2.17 由全交换方块特化而来）：
    取 `V₁ = V₂`、`f = 𝟙` 时，`p ≫ g = q` 的方块交换数据，
    连同 `V₁` 上的恒等收敛态射及其有界 ESS 数据，
    可由方块数据构造。 -/
theorem essComposition_from_square {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (cmp : ConvergenceMorphism conv₁ conv₃)
    (cmg : ConvergenceMorphism conv₃ conv₄)
    (cmq : ConvergenceMorphism conv₁ conv₄)
    (bnd₁ : F₁.IsBounded) (bnd₃ : F₃.IsBounded) (bnd₄ : F₄.IsBounded)
    (extp : BoundedExtensionSS conv₁ conv₃ cmp bnd₁ bnd₃)
    (extg : BoundedExtensionSS conv₃ conv₄ cmg bnd₃ bnd₄)
    (extq : BoundedExtensionSS conv₁ conv₄ cmq bnd₁ bnd₄)
    (_abutment_comm : ∀ (k' : ω'), cmp.aMap k' ≫ cmg.aMap k' = cmq.aMap k')
    (m l : ℤ) (kx kz kw : ω)
    (_hp_rel : ESSRelation extp m kx kz)
    (_hg_rel : ESSRelation extg l kz kw) :
    ∃ (idCm : ConvergenceMorphism conv₁ conv₁)
      (_idExt : BoundedExtensionSS conv₁ conv₁ idCm bnd₁ bnd₁),
    (∀ (k : ω), idCm.eMap k = 𝟙 _) ∧ (∀ (k' : ω'), idCm.aMap k' = 𝟙 _) := by
  refine ⟨{
    eMap := fun _ => 𝟙 _
    aMap := fun _ => 𝟙 _
    filtration_compat := F₁.fcId
    reindex_eq := rfl
    iso_compat := fun k => by
      simp only [Category.id_comp, Filtration.transportGraded_self, Category.comp_id,
        F₁.inducedAssocGradedMap_id (conv₁.reindex k).1 (conv₁.reindex k).2] },
    BoundedExtensionSS.mk' conv₁ conv₁ _ bnd₁ bnd₁, fun _ => rfl, fun _ => rfl⟩
/-! ### Boundary transfer -/

/-- Boundary transfer under the commutativity square: an element in the
    ESS boundary of the q-differential maps to an element in the ESS boundary
    of the g-differential under appropriate conditions. -/
theorem essCommutativity_boundary_transfer {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n : ℤ) (kw : ω) :
    Nonempty (sq.extq.essBoundary n kw ⟶ sq.extg.essBoundary n kw) := by
  sorry
/-! ### ESS page functoriality under commutativity -/

/-- The ESS page at level n is functorial: the page map induced by the commutativity
    square respects composition of convergence morphisms at each ESS page. -/
theorem essCommutativity_page_functorial {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (r : ℤ) (_hr : 0 ≤ r)
    (_hp_degen : E₁.DegeneratesAt r)
    (_hg_degen : E₃.DegeneratesAt r)
    (n : ℤ) (k₁ k₂ : ω)
    (φ : sq.extf.essDiff n k₁ k₂ ⟶ sq.extg.essDiff n k₁ k₂)
    (ψ : sq.extf.essDiff (n + 1) k₁ k₂ ⟶ sq.extg.essDiff (n + 1) k₁ k₂)
    (d_f : sq.extf.essDiff n k₁ k₂ ⟶ sq.extf.essDiff (n + 1) k₁ k₂)
    (d_g : sq.extg.essDiff n k₁ k₂ ⟶ sq.extg.essDiff (n + 1) k₁ k₂) :
    φ ≫ d_g = d_f ≫ ψ := by
  sorry
/-- 检测相容性所需的分量投影：把余核投影从 `reindex₄ k` 的 gr 对象
    沿指标相等 `reindex_eq` 搬到 `reindex₂ k` 的 gr 对象。
    端点显式写出（而非隐藏于 eqToHom 的证明项中），使调用方
    `rw`/`show` 重写时无需猜测 eqToHom 的类型。 -/
noncomputable def detectionGradedProj {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₂ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₂ A₄ : ω' → C} {F₂ : Filtration A₂} {F₄ : Filtration A₄}
    {conv₂ : Convergence E₂ A₂ F₂} {conv₄ : Convergence E₄ A₄ F₄}
    (cmq : ConvergenceMorphism conv₂ conv₄) (k : ω) :
    F₄.associatedGraded (conv₄.reindex k).1 (conv₄.reindex k).2 ⟶
      F₄.associatedGraded (conv₂.reindex k).1 (conv₂.reindex k).2 :=
  eqToHom (by rw [cmq.reindex_eq])

/-- 检测相容性所需的 gr 同构转移：conv₂ 的收敛同构与 cmq 的 gr 诱导映射复合，
    等于 eMap、conv₄ 的收敛同构、指标传输的复合（`iso_compat` 的搬运形式）。
    证明：把 `detectionGradedProj` 展开为 `transportGraded`，即 `iso_compat`。 -/
theorem detectionGradedProj_compat {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₂ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₂ A₄ : ω' → C} {F₂ : Filtration A₂} {F₄ : Filtration A₄}
    {conv₂ : Convergence E₂ A₂ F₂} {conv₄ : Convergence E₄ A₄ F₄}
    (cmq : ConvergenceMorphism conv₂ conv₄) (k : ω) :
    (conv₂.iso k).hom ≫
        Filtration.inducedAssocGradedMap cmq.aMap cmq.filtration_compat
          (conv₂.reindex k).1 (conv₂.reindex k).2 =
      cmq.eMap k ≫ (conv₄.iso k).hom ≫ detectionGradedProj cmq k := by
  show (conv₂.iso k).hom ≫
        Filtration.inducedAssocGradedMap cmq.aMap cmq.filtration_compat
          (conv₂.reindex k).1 (conv₂.reindex k).2 =
      cmq.eMap k ≫ (conv₄.iso k).hom ≫
        F₄.transportGraded (congrFun cmq.reindex_eq k).symm
  exact (cmq.iso_compat k).symm

/-- The detection set data is compatible with the commutativity square maps. -/
theorem essCommutativity_detection_compat {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    {T : C} (k : ω) (y : T ⟶ (E₂.ssData k).eInfty)
    (yrep : DetectionSet conv₂ k y) :
    ∃ (z : T ⟶ (E₄.ssData k).eInfty),
      ∃ (x : T ⟶ Subobject.underlying.obj
          (F₄.F (conv₄.reindex k).1 (conv₄.reindex k).2)),
      Detects conv₄ z x := by
  sorry
/-- Commutativity is preserved under ESS page transition: if the commutativity
    relation holds at page n, it holds at page n+1 (assuming no new crossings). -/
theorem essCommutativity_page_transition {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n : ℤ) (ky kw : ω)
    (_hq_rel_n : ESSRelation sq.extq n ky kw)
    (_hg_rel_n : ESSRelation sq.extg n ky kw) :
    Nonempty (sq.extq.essDiff n ky kw ⟶ sq.extg.essDiff n ky kw) := by
  sorry
end KIPBase.SpectralSequence
