/-
  KIPBase.SpectralSequence.Convergence
  §1.2 Convergence of spectral sequences — filtrations, graded pieces,
  detection, category of converging spectral sequences

  Blueprint: prerequisites.tex §1.2 (filtration through detect-difference)
  Informal:  informal/spectral_sequences.md §Convergence.lean

  All filtrations are decreasing. Convergence is in the weak sense
  (no strong convergence considerations).
-/
import KIPBase.Mathlib
import KIPBase.SpectralSequence.Basic

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Filtrations

A decreasing filtration on a graded object `A : ω → C` is a family of
subobjects `F^s A^k ≤ A^k` indexed by `s : ℤ` and `k : ω`, such that
`F^{s+1} A^k ≤ F^s A^k` for all `s`, `k`. -/

/-- A decreasing filtration on a graded object `A : ω → C`.
    `F s k` is the subobject `F^s A^k ≤ A^k`. Monotonicity says
    `F^{s+1} ≤ F^s` (decreasing filtration). -/
structure Filtration {ω : Type w} (A : ω → C) where
  /-- The subobject `F^s A^k` of `A k` at filtration level `s`. -/
  F : ℤ → (k : ω) → Subobject (A k)
  /-- Filtration is decreasing: `F^{s+1} ≤ F^s`. -/
  mono : ∀ (s : ℤ) (k : ω), F (s + 1) k ≤ F s k

/-- A filtration is bounded if for each `k`, there exist bounds `a ≤ b`
    such that `F^s A^k = A^k` for `s ≤ a` and `F^s A^k = 0` for `s ≥ b`. -/
structure Filtration.IsBounded {ω : Type w} {A : ω → C}
    (fil : Filtration A) where
  /-- Lower bound: for `s ≤ lo k`, the filtration is everything. -/
  lo : ω → ℤ
  /-- Upper bound: for `s ≥ hi k`, the filtration is trivial. -/
  hi : ω → ℤ
  /-- `lo ≤ hi`. -/
  lo_le_hi : ∀ (k : ω), lo k ≤ hi k
  /-- `F^s = A` for `s ≤ lo`. -/
  boundedBelow : ∀ (k : ω) (s : ℤ), s ≤ lo k → fil.F s k = ⊤
  /-- `F^s = 0` for `s ≥ hi`. -/
  boundedAbove : ∀ (k : ω) (s : ℤ), hi k ≤ s → fil.F s k = ⊥

/-! ### Associated graded

The associated graded of a filtration is the family of quotients
`gr^s A^k = F^s A^k / F^{s+1} A^k`, defined as the cokernel of the
inclusion `F^{s+1} ↪ F^s` obtained from monotonicity. -/

/-- The associated graded `gr^s A^k = F^s A^k / F^{s+1} A^k`, defined as
    the cokernel of the inclusion `F^{s+1} ↪ F^s`. -/
noncomputable def Filtration.associatedGraded {ω : Type w} {A : ω → C}
    (fil : Filtration A) (s : ℤ) (k : ω) : C :=
  cokernel (Subobject.ofLE (fil.F (s + 1) k) (fil.F s k) (fil.mono s k))

/-- The projection morphism `F^s A^k ⟶ gr^s A^k = F^s / F^{s+1}`. -/
noncomputable def Filtration.toAssociatedGraded {ω : Type w} {A : ω → C}
    (fil : Filtration A) (s : ℤ) (k : ω) :
    Subobject.underlying.obj (fil.F s k) ⟶ fil.associatedGraded s k :=
  cokernel.π (Subobject.ofLE (fil.F (s + 1) k) (fil.F s k) (fil.mono s k))

/-- 沿指标相等的 gr 对象传输：把 `h : r₁ = r₂` 提升为
    `F.associatedGraded r₁ ⟶ F.associatedGraded r₂` 的态射。
    这是 `eqToHom` 的打包形式：端点在定义类型中直接陈述为
    `F.associatedGraded rᵢ.1 rᵢ.2`（常值头应用，而非 `congrArg` 产生的
    β-红式），使 `≫` 的类型检查命中语法快路径，
    避免 `isDefEq` 展开 `associatedGraded → cokernel → colimit` 实例树而爆炸。 -/
noncomputable def Filtration.transportGraded {ω' : Type w} {A : ω' → C}
    (F : Filtration A) {r₁ r₂ : ℤ × ω'} (h : r₁ = r₂) :
    F.associatedGraded r₁.1 r₁.2 ⟶ F.associatedGraded r₂.1 r₂.2 :=
  eqToHom (by rw [h])

/-- 自反指标处的传输是恒等态射。
    证明：`transportGraded` 展开为 `eqToHom`，自反等式上它定义上等于 `𝟙`。 -/
lemma Filtration.transportGraded_self {ω' : Type w} {A : ω' → C} (F : Filtration A)
    {r : ℤ × ω'} (h : r = r) :
    F.transportGraded h = 𝟙 (F.associatedGraded r.1 r.2) :=
  rfl

/-- 传输的复合性：两段传输的复合等于指标等式传递后的传输。
    证明：消去两段等式后，两边均化归为恒等态射。 -/
lemma Filtration.transportGraded_trans {ω' : Type w} {A : ω' → C} (F : Filtration A)
    {r₁ r₂ r₃ : ℤ × ω'} (h₁₂ : r₁ = r₂) (h₂₃ : r₂ = r₃) :
    F.transportGraded h₁₂ ≫ F.transportGraded h₂₃ = F.transportGraded (h₁₂.trans h₂₃) := by
  subst h₁₂
  subst h₂₃
  simp only [Filtration.transportGraded_self, Category.id_comp]

/-! ### Convergence

A spectral sequence `E` converges to a graded object `A` with filtration `F`
if the E∞-page is isomorphic to the associated graded `gr(A, F)`, up to
a linear reindexing of the grading.

This is *weak convergence* — the project does not consider strong convergence. -/

/-- A spectral sequence `E` converges to a graded object `A` equipped with
    filtration `F`. The `reindex` map specifies how the spectral sequence
    index `ω` maps to `(filtration degree, stem degree)`.
    The E∞-page is `(E.ssData k).eInfty = Z⊤/B⊤` from the SSData. -/
structure Convergence {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    (E : SpectralSequence C ω) {ω' : Type w} (A : ω' → C) (F : Filtration A) where
  /-- Reindexing: spectral sequence index → (filtration degree, stem degree). -/
  reindex : ω → ℤ × ω'
  /-- The reindexing map is a bijection. -/
  reindex_bijective : Function.Bijective reindex
  /-- Convergence isomorphism: `E∞^k ≅ gr^s A^{k'}` where `(s, k') = reindex k`. -/
  iso : ∀ (k : ω),
    (E.ssData k).eInfty ≅ F.associatedGraded (reindex k).1 (reindex k).2

/-! ### Stem and filtration degrees -/

/-- The filtration degree component of the convergence reindexing. -/
def Convergence.filtrationDegree {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ℤ :=
  (conv.reindex k).1

/-- The stem degree component of the convergence reindexing. -/
def Convergence.stemDegree {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ω' :=
  (conv.reindex k).2

/-! ### Induced maps on associated graded

A family of morphisms `aMap : A₁ k' ⟶ A₂ k'` that preserves filtrations
induces a map `gr^s(A₁) ⟶ gr^s(A₂)` on the associated graded pieces. -/

/-- The map induced on associated graded pieces by a filtration-compatible map.
    Given filtrations `F₁` on `A₁` and `F₂` on `A₂`, a family of morphisms
    `aMap : A₁ k' ⟶ A₂ k'` preserving the filtrations induces a map
    `gr^s(A₁, k') ⟶ gr^s(A₂, k')` on the associated graded via the
    universal property of cokernels. -/
noncomputable def Filtration.inducedAssocGradedMap {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
             Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (s : ℤ) (k' : ω') : F₁.associatedGraded s k' ⟶ F₂.associatedGraded s k' :=
  cokernel.map
    (Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k'))
    (Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (hcompat (s + 1) k').choose
    (hcompat s k').choose
    (by
      apply (cancel_mono ((F₂.F s k').arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(hcompat s k').choose_spec, (hcompat (s + 1) k').choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

/-! ### Category of converging spectral sequences

A morphism of converging spectral sequences consists of a morphism on the
E∞-pages and a morphism on the target graded objects, preserving
filtrations and compatible with convergence isomorphisms. -/

/-- 收敛谱序列态射的**数据部分**（data/proof 分离的第一半）：
    只含数据——E∞ 页映射族 `eMap`、极限对象映射族 `aMap`，
    以及 `aMap` 保过滤的存在见证 `filtration_compat`。
    `filtration_compat` 虽是 ∃-命题，但它是诱导 gr 映射 / 截断映射的**输入数据**
    （下游用 `.choose` 取出见证），故归入数据部分而非证明部分。
    与收敛同构的相容性等式（`reindex_eq`、`iso_compat`）属于证明部分，
    放在 `ConvergenceMorphism` 中（`extends` 本结构）。 -/
structure ConvergenceMorphismData {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂) where
  /-- The map on E∞-pages. -/
  eMap : ∀ (k : ω), (E₁.ssData k).eInfty ⟶ (E₂.ssData k).eInfty
  /-- The map on target graded objects. -/
  aMap : ∀ (k' : ω'), A₁ k' ⟶ A₂ k'
  /-- `aMap` preserves filtrations: `aMap(F₁^s) ⊆ F₂^s`.
      Formalized as: for each `s, k'`, the restriction of `aMap` to `F₁^s`
      factors through `F₂^s`. -/
  filtration_compat : ∀ (s : ℤ) (k' : ω'),
    ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
           Subobject.underlying.obj (F₂.F s k')),
      φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k'

/-- 收敛谱序列的**态射**（data/proof 分离的第二半）：
    `extends ConvergenceMorphismData`（数据部分），
    此处只附加**证明字段**——重指标一致性 `reindex_eq`
    与收敛同构相容性 `iso_compat`。
    注意：底层的谱序列态射 `ssMap` 不属于本结构；
    `eMap` 即为 E∞ 页上的态射数据（通常取某 `ssMap.eInftyMap`，但不强制）。 -/
structure ConvergenceMorphism {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    extends ConvergenceMorphismData conv₁ conv₂ where
  /-- The reindexings agree (so the morphism is well-defined). -/
  reindex_eq : conv₁.reindex = conv₂.reindex
  /-- Compatibility of `eMap` and `aMap` with the convergence isomorphisms.
      For each `k`, the diagram
      ```
      (E₁.ssData k).eInfty --[eMap k]--> (E₂.ssData k).eInfty
          |                                     |
        iso₁(k)                               iso₂(k)
          v                                     v
      gr^s(A₁, k')      --[grMap]-->      gr^s(A₂, k')
      ```
      commutes, where `(s, k') = reindex k` and `grMap` is the map on
      associated graded pieces induced by `aMap` via `filtration_compat`.
      The `transportGraded` map transports `conv₂.iso` from
      `conv₂.reindex`-indices to `conv₁.reindex`-indices using `reindex_eq`
      （`eqToHom` 的打包形式，端点无 β-红式，避免 `≫` 类型检查的
      `isDefEq` 爆炸）。
      证明字段只含 `reindex_eq` 与收敛相容性 `iso_compat`。 -/
  iso_compat : ∀ (k : ω),
    eMap k ≫ (conv₂.iso k).hom ≫
      F₂.transportGraded (congrFun reindex_eq k).symm =
    (conv₁.iso k).hom ≫
      Filtration.inducedAssocGradedMap aMap filtration_compat
        (conv₁.reindex k).1 (conv₁.reindex k).2

/-! ### Detection

An element `y ∈ E∞^k` **detects** an element `x` of `A^{k'}` of filtration ≥ s,
meaning: `x` lies in `F^s A^{k'}`, and its image in `gr^s A^{k'} = F^s/F^{s+1}`
corresponds to `y` under the convergence isomorphism.

Elements are modeled as generalized elements (morphisms from a test object `T`). -/

/-- `Detects conv y x` means that the generalized element `y : T ⟶ E∞^k`
    detects the generalized element `x : T ⟶ F^s A^{k'}`, where
    `(s, k') = conv.reindex k`. Concretely:
    `y ≫ iso(k) = x ≫ π` where `π : F^s → gr^s = F^s/F^{s+1}`. -/
def Detects {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ (E.ssData k).eInfty)
    (x : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2))
    : Prop :=
  y ≫ (conv.iso k).hom =
    x ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2

/-! ### Detection propositions -/

/-- **detect_zero** (Blueprint §1.2): An element `x` of filtration ≥ s is detected
    by `0 ∈ E∞` if and only if `x` actually has filtration ≥ s+1.

    That is, `x ∈ F^s A^k` maps to zero in `gr^s = F^s/F^{s+1}` iff `x`
    lifts to `F^{s+1}`. -/
theorem detect_zero {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (x : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2))
    : Detects conv (0 : T ⟶ (E.ssData k).eInfty) x ↔
      ∃ (x' : T ⟶ Subobject.underlying.obj
            (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)),
        x' ≫ Subobject.ofLE
          (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
          (F.F (conv.reindex k).1 (conv.reindex k).2)
          (F.mono (conv.reindex k).1 (conv.reindex k).2) = x := by
  simp only [Detects, Filtration.toAssociatedGraded, Filtration.associatedGraded, Limits.zero_comp]
  constructor
  · intro h
    exact ⟨Abelian.monoLift _ x (by rw [h]), Abelian.monoLift_comp _ x (by rw [h])⟩
  · rintro ⟨x', hx'⟩
    rw [← hx', Category.assoc, cokernel.condition, Limits.comp_zero]

/-- **detect_difference** (Blueprint §1.2): Two elements `x, x'` of filtration ≥ s
    are detected by the same `y ∈ E∞` if and only if their difference `x - x'`
    has filtration ≥ s+1.

    That is, `x` and `x'` project to the same element in `gr^s` iff `x - x'`
    lifts to `F^{s+1}`. -/
theorem detect_difference {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ (E.ssData k).eInfty)
    (x x' : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2))
    : (Detects conv y x ∧ Detects conv y x') ↔
      (Detects conv y x ∧
        ∃ (z : T ⟶ Subobject.underlying.obj
              (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)),
          z ≫ Subobject.ofLE
            (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
            (F.F (conv.reindex k).1 (conv.reindex k).2)
            (F.mono (conv.reindex k).1 (conv.reindex k).2) = x - x') := by
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have key : (x - x') ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2 = 0 := by
      rw [Detects] at hx hx'
      rw [Preadditive.sub_comp, sub_eq_zero]
      exact hx.symm.trans hx'
    simp only [Filtration.toAssociatedGraded] at key
    exact ⟨Abelian.monoLift _ (x - x') key, Abelian.monoLift_comp _ (x - x') key⟩
  · rintro ⟨hx, z, hz⟩
    refine ⟨hx, ?_⟩
    change y ≫ (conv.iso k).hom = x' ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2
    have hd : Detects conv y x := hx
    rw [Detects] at hd
    have hx'eq : x' = x - z ≫ Subobject.ofLE
        (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
        (F.F (conv.reindex k).1 (conv.reindex k).2)
        (F.mono (conv.reindex k).1 (conv.reindex k).2) := by
      rw [hz, sub_sub_cancel]
    rw [hx'eq, Preadditive.sub_comp, hd]
    simp only [Category.assoc, Filtration.toAssociatedGraded, cokernel.condition, Limits.comp_zero,
      sub_zero]

/-! ### One-sided filtration conditions

Bounded below and bounded above are the one-sided analogues of `IsBounded`.
A bounded filtration is both bounded below and bounded above. -/

/-- A filtration is **bounded below** if for each `k`, the filtration eventually
    covers everything from below: `∃ s₀, ∀ s ≤ s₀, F^s A^k = ⊤`. -/
structure Filtration.IsBoundedBelow {ω : Type w} {A : ω → C}
    (fil : Filtration A) where
  lo : ω → ℤ
  boundedBelow : ∀ (k : ω) (s : ℤ), s ≤ lo k → fil.F s k = ⊤

/-- A filtration is **bounded above** if for each `k`, the filtration eventually
    becomes trivial from above: `∃ s₀, ∀ s ≥ s₀, F^s A^k = ⊥`. -/
structure Filtration.IsBoundedAbove {ω : Type w} {A : ω → C}
    (fil : Filtration A) where
  hi : ω → ℤ
  boundedAbove : ∀ (k : ω) (s : ℤ), hi k ≤ s → fil.F s k = ⊥

/-- A bounded filtration is bounded below. -/
def Filtration.IsBounded.toIsBoundedBelow {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBounded) : fil.IsBoundedBelow where
  lo := hb.lo
  boundedBelow := hb.boundedBelow

/-- A bounded filtration is bounded above. -/
def Filtration.IsBounded.toIsBoundedAbove {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBounded) : fil.IsBoundedAbove where
  hi := hb.hi
  boundedAbove := hb.boundedAbove

/-! ### True exhaustive and Hausdorff conditions

These are the standard mathematical definitions, weaker than bounded below/above. -/

/-- A filtration is **exhaustive** if for each `k`, every element eventually lies
    in some filtration level: `∀ k, ∃ s, F^s A^k = ⊤`.
    This is weaker than `IsBoundedBelow` (which gives a uniform bound). -/
def Filtration.IsExhaustive {ω : Type w} {A : ω → C}
    (fil : Filtration A) : Prop :=
  ∀ (k : ω), ∃ (s : ℤ), fil.F s k = ⊤

/-- A filtration is **Hausdorff** (separated) if for each `k`, the filtration
    eventually becomes trivial: `∀ k, ∃ s, F^s A^k = ⊥`.
    This is weaker than `IsBoundedAbove` (which gives a uniform bound). -/
def Filtration.IsHausdorff {ω : Type w} {A : ω → C}
    (fil : Filtration A) : Prop :=
  ∀ (k : ω), ∃ (s : ℤ), fil.F s k = ⊥

omit [Abelian C] in
/-- A filtration bounded below is exhaustive. -/
theorem Filtration.IsBoundedBelow.toIsExhaustive {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBoundedBelow) : fil.IsExhaustive := by
  intro k; exact ⟨hb.lo k, hb.boundedBelow k (hb.lo k) le_rfl⟩

/-- A filtration bounded above is Hausdorff. -/
theorem Filtration.IsBoundedAbove.toIsHausdorff {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBoundedAbove) : fil.IsHausdorff := by
  intro k; exact ⟨hb.hi k, hb.boundedAbove k (hb.hi k) le_rfl⟩

/-! ### Filtered morphisms

A morphism between filtered graded objects that preserves filtration. -/

/-- A filtered morphism between graded objects `A₁` and `A₂` with filtrations
    `F₁` and `F₂` consists of a degreewise map that preserves filtrations:
    the restriction of `map k` to `F₁^s A₁^k` factors through `F₂^s A₂^k`. -/
structure FilteredMorphism {ω : Type w} {A₁ A₂ : ω → C}
    (F₁ : Filtration A₁) (F₂ : Filtration A₂) where
  map : ∀ (k : ω), A₁ k ⟶ A₂ k
  compat : ∀ (s : ℤ) (k : ω),
    ∃ (φ : Subobject.underlying.obj (F₁.F s k) ⟶
           Subobject.underlying.obj (F₂.F s k)),
      φ ≫ (F₂.F s k).arrow = (F₁.F s k).arrow ≫ map k

/-- A filtered morphism induces a map on associated graded pieces. -/
noncomputable def FilteredMorphism.inducedGrMap {ω : Type w} {A₁ A₂ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (f : FilteredMorphism F₁ F₂) (s : ℤ) (k : ω) :
    F₁.associatedGraded s k ⟶ F₂.associatedGraded s k :=
  Filtration.inducedAssocGradedMap f.map f.compat s k

/-! ### 收敛谱序列的范畴

`ConvergingSS` 打包一个谱序列连同其极限（分次对象 + 过滤 + 收敛结构），
态射为 data/proof 分离的 `ConvergenceMorphism`。 -/

/-- **收敛谱序列**：谱序列 `E` 连同极限分次对象 `A`、其上的过滤 `F`
    与收敛结构 `conv`（`E∞ ≅ gr(A,F)`，相差一个重指标）。 -/
structure ConvergingSS (C : Type u) [Category.{v} C] [Abelian C]
    (ω : Type w) [AddCommGroup ω] [DecidableEq ω] (ω' : Type w) where
  /-- 底层谱序列 -/
  E : SpectralSequence C ω
  /-- 极限分次对象 -/
  A : ω' → C
  /-- 极限对象上的过滤 -/
  F : Filtration A
  /-- 收敛结构：`E∞ ≅ gr(A, F)` -/
  conv : Convergence E A F

/-- 收敛谱序列态射的外延性：两态射 `eMap`、`aMap` 相同则相等。
    重指标相等 `reindex_eq` 与相容性 `iso_compat` 是 Prop（proof irrelevance），
    `filtration_compat` 是 ∃-命题（也是 Prop）；用 cases 沿 extends 链
    逐层消去构造子，得到 eMap/aMap 两个方程后 subst 即 rfl。 -/
@[ext]
theorem ConvergenceMorphism.ext {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {f g : ConvergenceMorphism conv₁ conv₂}
    (he : f.eMap = g.eMap) (ha : f.aMap = g.aMap) : f = g := by
  cases f with | mk f_data f_re f_iso => ?_
  cases f_data with | mk f_e f_a f_fil => ?_
  cases g with | mk g_data g_re g_iso => ?_
  cases g_data with | mk g_e g_a g_fil => ?_
  simp only [mk.injEq] at he ha
  subst he
  subst ha
  rfl

/-! ### 收敛谱序列范畴的辅助构造

下面三个定义/引理把范畴实例中最容易卡死的部分抽出来单独证明：
(1) 恒等态射的过滤提升恒取恒等（`fcId`）；
(2) 复合态射的过滤提升取两次提升的复合（`fcComp`，采用
    `Basic.lean` 中 `PreSS` 范畴复合同款 `choose` 风格——
    `Exists.elim` 版本无法与目标中的 `choose` 项连起来）；
(3) 诱导 gr 映射的函子性：恒等诱导恒等、复合诱导复合。
    两条都用 `cancel_epi (cokernel.π _)` 消去余核投影，
    展开 `cokernel.map` 后用 `cancel_mono arrow` 比较提升见证。 -/

/-- 恒等 `aMap` 的过滤兼容性数据：提升直接取恒等。 -/
def Filtration.fcId {ω' : Type w} {A : ω' → C} (F : Filtration A)
    (s : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj (F.F s k') ⟶ Subobject.underlying.obj (F.F s k')),
      φ ≫ (F.F s k').arrow = (F.F s k').arrow ≫ 𝟙 _ :=
  ⟨𝟙 _, by simp⟩

/-- 复合 `aMap` 的过滤兼容性数据：提升取两次提升的复合
    （与 `Basic.lean` 中 PreSS 范畴复合的 `choose` 提升同款）。 -/
def ConvergenceMorphismData.fcComp {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (f : ConvergenceMorphism conv₁ conv₂) (g : ConvergenceMorphism conv₂ conv₃)
    (s : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶ Subobject.underlying.obj (F₃.F s k')),
      φ ≫ (F₃.F s k').arrow = (F₁.F s k').arrow ≫ (f.aMap k' ≫ g.aMap k') :=
  ⟨(f.filtration_compat s k').choose ≫ (g.filtration_compat s k').choose, by
    rw [Category.assoc, (g.filtration_compat s k').choose_spec,
      ← Category.assoc, (f.filtration_compat s k').choose_spec, Category.assoc]⟩

/-- 广义诱导 gr 映射：把提升族 `φ` 与相容性证明 `hw` 作为**显式参数**
    （而非从 ∃-见证中 `.choose`）。
    与 `inducedAssocGradedMap` 数学上相同，但显式参数版本在后续
    `rw`/`congr` 推理中不会触发"依赖证明项导致 motive 不类型正确"的障碍。 -/
noncomputable def Filtration.inducedGradedMapOfMap {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (φ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k'))
    (hw : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫ Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (s : ℤ) (k' : ω') : F₁.associatedGraded s k' ⟶ F₂.associatedGraded s k' :=
  cokernel.map
    (Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k'))
    (Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (φ (s + 1) k') (φ s k') (hw s k')

/-- 广义诱导 gr 映射的同余性：提升族相等则诱导映射相等
    （证明项由 proof irrelevance 自动等同）。 -/
lemma Filtration.inducedGradedMapOfMap_congr {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {φ ψ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k')}
    (hwφ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫ Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (hwψ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ ψ s k' =
        ψ (s + 1) k' ≫ Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (h : φ = ψ) (s : ℤ) (k' : ω') :
    Filtration.inducedGradedMapOfMap φ hwφ s k' =
      Filtration.inducedGradedMapOfMap ψ hwψ s k' := by
  subst h
  rfl

/-- 广义诱导 gr 映射的恒等性：恒等提升诱导恒等映射。
    证明：用 `cokernel.π` 的外满性消去，展开 `cokernel.map` 后
    把 `associatedGraded` 展开为 `cokernel _`，使 `Category.comp_id` 能匹配。 -/
lemma Filtration.inducedGradedMapOfMap_id {ω' : Type w} {A : ω' → C}
    (F : Filtration A) (s : ℤ) (k' : ω')
    (hw : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F.F (s + 1) k') (F.F s k') (F.mono s k') ≫ 𝟙 _ =
        (𝟙 _ : Subobject.underlying.obj (F.F (s + 1) k') ⟶ _) ≫
          Subobject.ofLE (F.F (s + 1) k') (F.F s k') (F.mono s k')) :
    Filtration.inducedGradedMapOfMap (fun s k' => 𝟙 _) hw s k' =
      𝟙 (F.associatedGraded s k') := by
  haveI := Classical.decEq ω'
  apply (cancel_epi (cokernel.π _)).mp
  simp only [Filtration.inducedGradedMapOfMap, cokernel.map, cokernel.π_desc,
    Category.id_comp]
  show cokernel.π _ = cokernel.π _ ≫ 𝟙 (cokernel _)
  simp only [Category.comp_id]

/-- 广义诱导 gr 映射的复合性：复合提升诱导复合映射。
    证明：用 `cokernel.π` 外满性消去，展开 `cokernel.map` 后用
    `cokernel.π_desc_assoc` / `cokernel.π_desc` / `Category.assoc` 化简即得。 -/
lemma Filtration.inducedGradedMapOfMap_comp {ω' : Type w} {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    (φ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k'))
    (ψ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₂.F s k') ⟶
      Subobject.underlying.obj (F₃.F s k'))
    (hwφ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫ Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (hwψ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k') ≫ ψ s k' =
        ψ (s + 1) k' ≫ Subobject.ofLE (F₃.F (s + 1) k') (F₃.F s k') (F₃.mono s k'))
    (hwφψ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ (φ s k' ≫ ψ s k') =
        (φ (s + 1) k' ≫ ψ (s + 1) k') ≫
          Subobject.ofLE (F₃.F (s + 1) k') (F₃.F s k') (F₃.mono s k'))
    (s : ℤ) (k' : ω') :
    Filtration.inducedGradedMapOfMap (fun s k' => φ s k' ≫ ψ s k') hwφψ s k' =
      Filtration.inducedGradedMapOfMap φ hwφ s k' ≫
        Filtration.inducedGradedMapOfMap ψ hwψ s k' := by
  haveI := Classical.decEq ω'
  apply (cancel_epi (cokernel.π _)).mp
  simp only [Filtration.inducedGradedMapOfMap, cokernel.map, cokernel.π_desc_assoc,
    cokernel.π_desc, Category.assoc]

/-- choose 风格提升族的相容性证明：从 ∃-见证的 `choose_spec` 直接推出
    广义诱导映射所需的 `ofLE ≫ φ = φ ≫ ofLE` 形状。
    由 `cancel_mono arrow` 归结到两个 `choose_spec` 的链式改写。 -/
lemma Filtration.choose_compat {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
             Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (s : ℤ) (k' : ω') :
    Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫
        (hcompat s k').choose =
      (hcompat (s + 1) k').choose ≫
        Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k') := by
  apply (cancel_mono ((F₂.F s k').arrow)).mp
  simp only [Category.assoc, Subobject.ofLE_arrow]
  rw [(hcompat s k').choose_spec, (hcompat (s + 1) k').choose_spec,
    ← Category.assoc, Subobject.ofLE_arrow]

/-- 桥接引理：choose 版本的诱导 gr 映射等于广义版本在 choose 提升处的取值。
    两边定义相同（`cokernel.map` 同一组参数），由 `rfl` 即得；
    本引理的价值在于把 `.choose` 从 rw 目标中剥离到等式右端。 -/
lemma Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
             Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (s : ℤ) (k' : ω') :
    Filtration.inducedAssocGradedMap aMap hcompat s k' =
      Filtration.inducedGradedMapOfMap (fun s k' => (hcompat s k').choose)
        (Filtration.choose_compat aMap hcompat) s k' :=
  rfl

/-- 恒等过滤兼容数据诱导的 gr 映射就是恒等。
    证明：先经桥接引理转成广义诱导映射，再用 `congr` 引理把
    `fcId.choose`（由 `cancel_mono arrow` 知其等于 `𝟙`）替换为恒等提升，
    最后调用广义恒等引理。 -/
lemma Filtration.inducedAssocGradedMap_id {ω' : Type w} {A : ω' → C}
    (F : Filtration A) (s : ℤ) (k' : ω') :
    Filtration.inducedAssocGradedMap (fun k' => 𝟙 (A k')) (F.fcId) s k' =
      𝟙 (F.associatedGraded s k') := by
  rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap]
  have h : (fun s k' => (F.fcId s k').choose) =
      fun s k' => 𝟙 (Subobject.underlying.obj (F.F s k')) := by
    funext s k'
    apply (cancel_mono ((F.F s k').arrow)).mp
    rw [(F.fcId s k').choose_spec, Category.comp_id, Category.id_comp]
  rw [Filtration.inducedGradedMapOfMap_congr
    (Filtration.choose_compat (fun k' => 𝟙 (A k')) F.fcId)
    (fun s k' => by rw [Category.comp_id, Category.id_comp]) h s k']
  exact Filtration.inducedGradedMapOfMap_id F s k' _

/-- 诱导 gr 映射的复合性：复合 `aMap`（配 `fcComp` 提升数据）诱导的 gr 映射
    等于两次诱导 gr 映射的复合。
    证明：三处 `inducedAssocGradedMap` 均经桥接引理转成广义诱导映射，
    再用 `congr` 引理把 `fcComp.choose`（由 `cancel_mono arrow` 知其等于
    两次提升的复合）替换为复合提升，最后调用广义复合引理。 -/
lemma Filtration.inducedAssocGradedMap_comp {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (f : ConvergenceMorphism conv₁ conv₂) (g : ConvergenceMorphism conv₂ conv₃)
    (s : ℤ) (k' : ω') :
    Filtration.inducedAssocGradedMap (fun k' => f.aMap k' ≫ g.aMap k')
        (ConvergenceMorphismData.fcComp f g) s k' =
      Filtration.inducedAssocGradedMap f.aMap f.filtration_compat s k' ≫
        Filtration.inducedAssocGradedMap g.aMap g.filtration_compat s k' := by
  rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap
    (fun k' => f.aMap k' ≫ g.aMap k') (ConvergenceMorphismData.fcComp f g)]
  rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap f.aMap f.filtration_compat]
  rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap g.aMap g.filtration_compat]
  have h : (fun s k' => (ConvergenceMorphismData.fcComp f g s k').choose) =
      fun s k' => (f.filtration_compat s k').choose ≫ (g.filtration_compat s k').choose := by
    funext s k'
    apply (cancel_mono ((F₃.F s k').arrow)).mp
    rw [Category.assoc _ _ ((F₃.F s k').arrow),
      (ConvergenceMorphismData.fcComp f g s k').choose_spec,
      (g.filtration_compat s k').choose_spec]
    conv_rhs => rw [← Category.assoc _ _ (g.aMap k'),
      (f.filtration_compat s k').choose_spec]
    exact (Category.assoc _ _ _).symm
  rw [Filtration.inducedGradedMapOfMap_congr
    (Filtration.choose_compat _ (ConvergenceMorphismData.fcComp f g))
    (fun s k' => by
      apply (cancel_mono ((F₃.F s k').arrow)).mp
      simp only [Category.assoc]
      rw [(g.filtration_compat s k').choose_spec, ← Category.assoc _ _ (g.aMap k'),
        (f.filtration_compat s k').choose_spec, ← Category.assoc _ _ (g.aMap k'),
        ← Category.assoc _ ((F₁.F s k').arrow) (f.aMap k'), Subobject.ofLE_arrow,
        Subobject.ofLE_arrow, (g.filtration_compat (s + 1) k').choose_spec,
        ← Category.assoc _ _ (g.aMap k'), (f.filtration_compat (s + 1) k').choose_spec]) h s k']
  exact Filtration.inducedGradedMapOfMap_comp _ _ (Filtration.choose_compat f.aMap
    f.filtration_compat) (Filtration.choose_compat g.aMap g.filtration_compat) _ s k'

/-- 诱导 gr 映射与指标传输的交换（自然性）：
    先在 `r₁` 处诱导再沿 `h : r₁ = r₂` 传输，
    等于先传输再在 `r₂` 处诱导。
    陈述使用 `transportGraded`（端点为常值头应用），
    使 `≫` 的类型检查命中语法快路径。
    证明：消去 `h` 后两边传输均化归为恒等。 -/
lemma Filtration.inducedGradedMapOfMap_transportGraded {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (φ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k'))
    (hw : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫ Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    {r₁ r₂ : ℤ × ω'} (h : r₁ = r₂) :
    Filtration.inducedGradedMapOfMap φ hw r₁.1 r₁.2 ≫ F₂.transportGraded h =
      F₁.transportGraded h ≫ Filtration.inducedGradedMapOfMap φ hw r₂.1 r₂.2 := by
  subst h
  simp only [Filtration.transportGraded_self, Category.comp_id, Category.id_comp]

/-- 复合态射的收敛相容性（范畴实例中 `comp` 的 `iso_compat` 证明字段）。
    证明：把复合重指标的传输 `transportGraded` 拆成两段（`transportGraded_trans`），
    依次重写 `g.iso_compat`、传输-诱导交换（`inducedGradedMapOfMap_transportGraded`，
    经桥接引理把 `inducedAssocGradedMap` 定义上等同于广义诱导映射）、
    `f.iso_compat`，最后用 `inducedAssocGradedMap_comp` 收拢诱导 gr 映射的复合。
    全部结合方向调整均用显式参数的 `Category.assoc`，
    避免 `rw` 在默认右结合链上找不到模式。 -/
lemma ConvergenceMorphism.iso_compat_comp {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w} {X Y Z : ConvergingSS C ω ω'}
    (f : ConvergenceMorphism X.conv Y.conv) (g : ConvergenceMorphism Y.conv Z.conv)
    (k : ω) :
    (f.eMap k ≫ g.eMap k) ≫ (Z.conv.iso k).hom ≫
        Z.F.transportGraded ((congrFun (f.reindex_eq.trans g.reindex_eq) k).symm) =
      (X.conv.iso k).hom ≫
        Filtration.inducedAssocGradedMap (fun k' => f.aMap k' ≫ g.aMap k')
          (ConvergenceMorphismData.fcComp f g) (X.conv.reindex k).1 (X.conv.reindex k).2 := by
  have hsplit : Z.F.transportGraded ((congrFun (f.reindex_eq.trans g.reindex_eq) k).symm) =
      Z.F.transportGraded ((congrFun g.reindex_eq k).symm) ≫
        Z.F.transportGraded ((congrFun f.reindex_eq k).symm) := by
    rw [Filtration.transportGraded_trans]
  have hnat : Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
        (Y.conv.reindex k).1 (Y.conv.reindex k).2 ≫
        Z.F.transportGraded ((congrFun f.reindex_eq k).symm) =
      Y.F.transportGraded ((congrFun f.reindex_eq k).symm) ≫
        Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
          (X.conv.reindex k).1 (X.conv.reindex k).2 :=
    Filtration.inducedGradedMapOfMap_transportGraded
      (fun s k' => (g.filtration_compat s k').choose)
      (Filtration.choose_compat g.aMap g.filtration_compat)
      ((congrFun f.reindex_eq k).symm)
  rw [hsplit]
  simp only [Category.assoc]
  rw [← Category.assoc ((Z.conv.iso k).hom)
        (Z.F.transportGraded ((congrFun g.reindex_eq k).symm))
        (Z.F.transportGraded ((congrFun f.reindex_eq k).symm))]
  rw [← Category.assoc (g.eMap k)
        ((Z.conv.iso k).hom ≫ Z.F.transportGraded ((congrFun g.reindex_eq k).symm))
        (Z.F.transportGraded ((congrFun f.reindex_eq k).symm))]
  rw [g.iso_compat k]
  simp only [Category.assoc]
  rw [hnat]
  rw [← Category.assoc ((Y.conv.iso k).hom)
        (Y.F.transportGraded ((congrFun f.reindex_eq k).symm))
        (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
          (X.conv.reindex k).1 (X.conv.reindex k).2)]
  rw [← Category.assoc (f.eMap k)
        ((Y.conv.iso k).hom ≫ Y.F.transportGraded ((congrFun f.reindex_eq k).symm))
        (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
          (X.conv.reindex k).1 (X.conv.reindex k).2)]
  rw [f.iso_compat k]
  rw [Category.assoc ((X.conv.iso k).hom)
        (Filtration.inducedAssocGradedMap f.aMap f.filtration_compat
          (X.conv.reindex k).1 (X.conv.reindex k).2)
        (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
          (X.conv.reindex k).1 (X.conv.reindex k).2)]
  rw [← Filtration.inducedAssocGradedMap_comp f g (X.conv.reindex k).1 (X.conv.reindex k).2]

/-- 收敛谱序列的范畴结构：态射为 `ConvergenceMorphism`（data/proof 分离）。
    恒等态射的 eMap / aMap / 保过滤提升均取恒等（`fcId`），
    诱导 gr 映射为恒等（`inducedAssocGradedMap_id`）；
    复合的 eMap / aMap 逐分量复合，保过滤提升取两次提升的复合（`fcComp`），
    诱导 gr 映射满足复合性（`inducedAssocGradedMap_comp`），
    收敛相容性由 `ConvergenceMorphism.iso_compat_comp` 给出。
    范畴公理由 `ConvergenceMorphism.ext` 归约到 eMap / aMap 分量。 -/
noncomputable instance {ω : Type w} [AddCommGroup ω] [DecidableEq ω] {ω' : Type w} :
    Category.{max w v} (ConvergingSS C ω ω') where
  Hom X Y := ConvergenceMorphism X.conv Y.conv
  id X := ⟨
    { eMap := fun _ => 𝟙 _
      aMap := fun _ => 𝟙 _
      filtration_compat := X.F.fcId },
    rfl,
    fun k => by
      simp only [Category.id_comp, Filtration.transportGraded_self, Category.comp_id,
        X.F.inducedAssocGradedMap_id (X.conv.reindex k).1 (X.conv.reindex k).2,
        Category.comp_id]⟩
  comp {X Y Z} f g := ⟨
    { eMap := fun k => f.eMap k ≫ g.eMap k
      aMap := fun k' => f.aMap k' ≫ g.aMap k'
      filtration_compat := ConvergenceMorphismData.fcComp f g },
    f.reindex_eq.trans g.reindex_eq,
    fun k => by
      show (f.eMap k ≫ g.eMap k) ≫ (Z.conv.iso k).hom ≫
          Z.F.transportGraded ((congrFun (f.reindex_eq.trans g.reindex_eq) k).symm) =
        (X.conv.iso k).hom ≫
          Filtration.inducedAssocGradedMap (fun k' => f.aMap k' ≫ g.aMap k')
            (ConvergenceMorphismData.fcComp f g) (X.conv.reindex k).1 (X.conv.reindex k).2
      exact ConvergenceMorphism.iso_compat_comp f g k⟩
  id_comp f := ConvergenceMorphism.ext
    (funext fun _ => Category.id_comp _) (funext fun _ => Category.id_comp _)
  comp_id f := ConvergenceMorphism.ext
    (funext fun _ => Category.comp_id _) (funext fun _ => Category.comp_id _)
  assoc f g h := ConvergenceMorphism.ext
    (funext fun _ => Category.assoc _ _ _) (funext fun _ => Category.assoc _ _ _)

/-! ### Essential differentials

A differential `d_r` is essential at index `k` when it is nonzero.
The primary definition lives in `KIPBase.SpectralSequence.Crossing` as
`IsEssentialAt`. We do not duplicate it here. -/

end KIPBase.SpectralSequence
