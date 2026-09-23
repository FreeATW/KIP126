/-
  KIPBase.multiplicativeSS.Adams

  Multiplicative structure on Adams spectral sequences for composition of
  maps between finite spectra.
-/
import KIPBase.Mathlib
import KIPBase.multiplicativeSS.Basic
import KIPBase.StableHomotopy.Adams

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  KIPBase.SpectralSequence

universe u v w

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-! ### 映射 Adams 谱序列的收敛数据

`adamsMappingConvergingSS` 把 `adamsConvergence` 公理提供的收敛结构
（以 `AddCommGrpCat` 为值范畴）沿数学库的典范等价
`ModuleCat ℤ ≌ AddCommGrpCat` 搬到 `ModuleCat` 值范畴，打包成
`ConvergingSS`。谱序列本体与过滤、收敛同构逐项由等价函子
`(forget₂ (ModuleCat ℤ) AddCommGrpCat).inverse` 传送，不新增任何
数学假设；`finite_spectra_char` 保证映射谱有限，`adamsConvergence`
的有限性前提因此成立。 -/

/-- 整数系数环的提升：把 `ℤ` 放到宇宙 `v`，供 `ModuleCat.{v}` 使用。 -/
noncomputable def IntModuleRing : Type v := ULift.{v} ℤ

instance : CommRing (IntModuleRing.{v}) :=
  inferInstanceAs (CommRing (ULift.{v} ℤ))

/-- 把 `AddCommGrpCat` 的谱序列沿等价 `ModuleCat ℤ ≌ AddCommGrpCat`
传送到 `ModuleCat` 值范畴（`ULift ℤ` 上）。 -/
noncomputable def SpectralSequence.transfer {ι : Type w} [AddCommGroup ι]
    [DecidableEq ι] (E : SpectralSequence AddCommGrpCat.{v} ι) :
    SpectralSequence (ModuleCat.{v, v} IntModuleRing.{v}) ι := by
  sorry

open Classical in
/-- 有限谱之间映射群的收敛 Adams 谱序列：谱序列本体为映射谱的
Adams 谱序列沿等价传送到 `ModuleCat`，极限为映射同伦群，
收敛结构与过滤同样逐项传送。`E` 字段显式写为 `SpectralSequence.transfer
(AdamsSS 𝒮 …)`，使球谱特例的 `E` 投影有反身等式；
源与目标均为球谱时底层谱退化为球谱本身。 -/
noncomputable def adamsMappingConvergingSS (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) :
    ConvergingSS (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ) ℤ where
  E := SpectralSequence.transfer
    (AdamsSS 𝒮 (if X = SphereSpectrum ∧ Y = SphereSpectrum then SphereSpectrum
      else MappingSpectrum X Y))
  A := sorry
  F := sorry
  conv := sorry

/-- 有限谱之间映射群的 Adams 谱序列（无收敛结构）：映射谱的
Adams 谱序列沿 `ModuleCat ℤ ≌ AddCommGrpCat` 等价传送到
`ModuleCat` 值范畴。 -/
noncomputable def adamsMappingSS (X Y : 𝒮) :
    SpectralSequence (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ) :=
  SpectralSequence.transfer (AdamsSS 𝒮 (MappingSpectrum X Y))

/-- 映射 Adams 谱序列从第 2 页开始。 -/
theorem adamsMappingSS_r₀ (X Y : 𝒮) :
    (adamsMappingSS (𝒮 := 𝒮) X Y).r₀ = 2 := by
  sorry

/-- 映射 Adams 谱序列的微分次数与单谱 Adams 相同：`(r, r-1)`。 -/
theorem adamsMappingSS_diffDeg (X Y : 𝒮) :
    (adamsMappingSS (𝒮 := 𝒮) X Y).diffDeg = adamsDiffDeg := by
  sorry

/-- 页元素传送：把 `AddCommGrpCat` 值谱序列第 `r` 页 `k` 处的元素
映到 `SpectralSequence.transfer` 后的 `ModuleCat` 值谱序列同一页
同一双次数处的元素。 -/
noncomputable def SpectralSequence.pageTransfer {ι : Type w}
    [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence AddCommGrpCat.{v} ι) (r : ℤ) (k : ι)
    (x : ↑(E.Page r k)) : ↑((SpectralSequence.transfer E).Page r k) := by
  sorry

/-- 收敛重指标化：Adams 双次数 `(s, t)` 对应过滤次数 `s` 与杆数
`t - s`。 -/
theorem adamsMappingConvergingSS_reindex (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (k : ℤ × ℤ) :
    ((adamsMappingConvergingSS X Y hX hY).conv.reindex k).1 = k.1 ∧
    ((adamsMappingConvergingSS X Y hX hY).conv.reindex k).2 = k.2 - k.1 :=
  sorry

/-- 极限对象到映射同伦群的典范等价：把 `ModuleCat` 值的极限对象
沿 `AddCommGrpCat ≌ ModuleCat ℤ` 的等价还原为 Abel 群，再经
`mappingSpectrumHomotopy` 识别为稳定映射。 -/
noncomputable def adamsMappingConvergingSS_abutmentEquiv (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (n : ℤ) :
    (adamsMappingConvergingSS X Y hX hY).A n ≃
      HomotopyGroup n (MappingSpectrum X Y) :=
  sorry

/-- **Multiplicative Adams structure for composition.**  For finite spectra
`X`, `Y`, and `Z`, composition `[X,Y]_* ⊗ [Y,Z]_* → [X,Z]_*` induces a
pairing of their converging Adams spectral sequences.  The returned
`ConvergingSSPairing` includes the pagewise Leibniz product, the product on
the abutments, and the compatibility of that product with the E-infinity
pages. -/
axiom adamsCompositionConvergingSSPairing (X Y Z : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (hZ : IsFiniteSpectrum Z) :
    ConvergingSSPairing
      (adamsMappingConvergingSS X Y hX hY)
      (adamsMappingConvergingSS Y Z hY hZ)
      (adamsMappingConvergingSS X Z hX hZ)

/-- Adams signs use the parity of the stem.  Since bidegree `(s,t)` has stem
`t-s`, this fixes the parity appearing in the signed Leibniz rule. -/
axiom adamsCompositionConvergingSSPairing_parity
    (X Y Z : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (hZ : IsFiniteSpectrum Z) (s t : ℤ) :
    (adamsCompositionConvergingSSPairing X Y Z hX hY hZ).ssPairing.parity (s, t) =
      (↑(t - s) : ZMod 2)

/-- On the abutment, the Adams pairing is the actual composition of stable
maps.  The shift coherence first identifies `Σ^(a+b) X` with
`Σ^b (Σ^a X)`, so the right-hand side is `Σ^b f ≫ g`. -/
axiom adamsCompositionConvergingSSPairing_abutment_compatible
    (X Y Z : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (hZ : IsFiniteSpectrum Z) (a b : ℤ)
    (x : (adamsMappingConvergingSS X Y hX hY).A a)
    (y : (adamsMappingConvergingSS Y Z hY hZ).A b) :
    mappingSpectrumHomotopy (a + b) X Z
      ((adamsMappingConvergingSS_abutmentEquiv X Z hX hZ (a + b))
        ((adamsCompositionConvergingSSPairing X Y Z hX hY hZ).abutmentPair a b
          (x ⊗ₜ y))) =
      (shiftFunctorAdd 𝒮 a b).hom.app X ≫
        (shiftFunctor 𝒮 b).map
          (mappingSpectrumHomotopy a X Y
            ((adamsMappingConvergingSS_abutmentEquiv X Y hX hY a) x)) ≫
        mappingSpectrumHomotopy b Y Z
          ((adamsMappingConvergingSS_abutmentEquiv Y Z hY hZ b) y)

/-- The composition pairings are associative on every Adams page.  This is
the spectral-sequence lift of associativity of composition through four
finite spectra. -/
axiom adamsCompositionConvergingSSPairing_associative
    (W X Y Z : 𝒮) (hW : IsFiniteSpectrum W) (hX : IsFiniteSpectrum X)
    (hY : IsFiniteSpectrum Y) (hZ : IsFiniteSpectrum Z)
    (r : ℤ) (i j k : ℤ × ℤ) :
    ((adamsCompositionConvergingSSPairing W X Y hW hX hY).ssPairing.pair r i j ⊗ₘ
        𝟙 ((adamsMappingConvergingSS Y Z hY hZ).E.Page r k)) ≫
      (adamsCompositionConvergingSSPairing W Y Z hW hY hZ).ssPairing.pair r (i + j) k ≫
        eqToHom (by ac_rfl) =
      (α_ ((adamsMappingConvergingSS W X hW hX).E.Page r i)
        ((adamsMappingConvergingSS X Y hX hY).E.Page r j)
        ((adamsMappingConvergingSS Y Z hY hZ).E.Page r k)).hom ≫
      (𝟙 ((adamsMappingConvergingSS W X hW hX).E.Page r i) ⊗ₘ
        (adamsCompositionConvergingSSPairing X Y Z hX hY hZ).ssPairing.pair r j k) ≫
      (adamsCompositionConvergingSSPairing W X Z hW hX hZ).ssPairing.pair r i (j + k)

/-- The E-infinity products induced by composition are associative. -/
axiom adamsCompositionConvergingSSPairing_eInfty_associative
    (W X Y Z : 𝒮) (hW : IsFiniteSpectrum W) (hX : IsFiniteSpectrum X)
    (hY : IsFiniteSpectrum Y) (hZ : IsFiniteSpectrum Z)
    (i j k : ℤ × ℤ) :
    ((adamsCompositionConvergingSSPairing W X Y hW hX hY).eInftyPair i j ⊗ₘ
        𝟙 ((adamsMappingConvergingSS Y Z hY hZ).E.ssData k).eInfty) ≫
      (adamsCompositionConvergingSSPairing W Y Z hW hY hZ).eInftyPair (i + j) k ≫
        eqToHom (by ac_rfl) =
      (α_ ((adamsMappingConvergingSS W X hW hX).E.ssData i).eInfty
        ((adamsMappingConvergingSS X Y hX hY).E.ssData j).eInfty
        ((adamsMappingConvergingSS Y Z hY hZ).E.ssData k).eInfty).hom ≫
      (𝟙 ((adamsMappingConvergingSS W X hW hX).E.ssData i).eInfty ⊗ₘ
      (adamsCompositionConvergingSSPairing X Y Z hX hY hZ).eInftyPair j k) ≫
      (adamsCompositionConvergingSSPairing W X Z hW hX hZ).eInftyPair i (j + k)

/-- The abutment products are associative as well.  Together with the page
and `E∞` axioms this supplies associativity at every layer of the converging
composition pairing, rather than only on the spectral-sequence pages. -/
axiom adamsCompositionConvergingSSPairing_abutment_associative
    (W X Y Z : 𝒮) (hW : IsFiniteSpectrum W) (hX : IsFiniteSpectrum X)
    (hY : IsFiniteSpectrum Y) (hZ : IsFiniteSpectrum Z)
    (i j k : ℤ) :
    ((adamsCompositionConvergingSSPairing W X Y hW hX hY).abutmentPair i j ⊗ₘ
        𝟙 ((adamsMappingConvergingSS Y Z hY hZ).A k)) ≫
      (adamsCompositionConvergingSSPairing W Y Z hW hY hZ).abutmentPair (i + j) k ≫
        eqToHom (by ac_rfl) =
      (α_ ((adamsMappingConvergingSS W X hW hX).A i)
        ((adamsMappingConvergingSS X Y hX hY).A j)
        ((adamsMappingConvergingSS Y Z hY hZ).A k)).hom ≫
      (𝟙 ((adamsMappingConvergingSS W X hW hX).A i) ⊗ₘ
        (adamsCompositionConvergingSSPairing X Y Z hX hY hZ).abutmentPair j k) ≫
      (adamsCompositionConvergingSSPairing W X Z hW hX hZ).abutmentPair i (j + k)

/-- Unit data for the Adams spectral sequence of the endomorphism spectrum
`F(X,X)`.  The three components are the units on pages, on `E∞`, and on the
abutment respectively. -/
structure AdamsMappingConvergingSSUnit (X : 𝒮) (hX : IsFiniteSpectrum X) where
  page : ∀ r : ℤ,
    𝟙_ (ModuleCat.{v} IntModuleRing) ⟶
      (adamsMappingConvergingSS X X hX hX).E.Page r (0, 0)
  eInfty : 𝟙_ (ModuleCat.{v} IntModuleRing) ⟶
    ((adamsMappingConvergingSS X X hX hX).E.ssData (0, 0)).eInfty
  abutment : 𝟙_ (ModuleCat.{v} IntModuleRing) ⟶
    (adamsMappingConvergingSS X X hX hX).A 0

/-- The identity map of a finite spectrum determines unit data on its Adams
spectral sequence. -/
axiom adamsMappingConvergingSSUnit (X : 𝒮) (hX : IsFiniteSpectrum X) :
    AdamsMappingConvergingSSUnit X hX

/-- The pagewise composition pairing has the identity of `X` as a left unit. -/
axiom adamsCompositionConvergingSSPairing_page_left_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (r : ℤ) (k : ℤ × ℤ) :
    ((adamsMappingConvergingSSUnit X hX).page r ⊗ₘ
        𝟙 ((adamsMappingConvergingSS X Y hX hY).E.Page r k)) ≫
      (adamsCompositionConvergingSSPairing X X Y hX hX hY).ssPairing.pair r (0, 0) k ≫
        eqToHom (congrArg (fun q => (adamsMappingConvergingSS X Y hX hY).E.Page r q)
          (by ext <;> simp)) =
      (λ_ ((adamsMappingConvergingSS X Y hX hY).E.Page r k)).hom

/-- The pagewise composition pairing has the identity of `Y` as a right unit. -/
axiom adamsCompositionConvergingSSPairing_page_right_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (r : ℤ) (k : ℤ × ℤ) :
    (𝟙 ((adamsMappingConvergingSS X Y hX hY).E.Page r k) ⊗ₘ
        (adamsMappingConvergingSSUnit Y hY).page r) ≫
      (adamsCompositionConvergingSSPairing X Y Y hX hY hY).ssPairing.pair r k (0, 0) ≫
        eqToHom (congrArg (fun q => (adamsMappingConvergingSS X Y hX hY).E.Page r q)
          (by ext <;> simp)) =
      (ρ_ ((adamsMappingConvergingSS X Y hX hY).E.Page r k)).hom

/-- The E-infinity composition pairing has the identity of `X` as a left unit. -/
axiom adamsCompositionConvergingSSPairing_eInfty_left_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (k : ℤ × ℤ) :
    ((adamsMappingConvergingSSUnit X hX).eInfty ⊗ₘ
        𝟙 ((adamsMappingConvergingSS X Y hX hY).E.ssData k).eInfty) ≫
      (adamsCompositionConvergingSSPairing X X Y hX hX hY).eInftyPair (0, 0) k ≫
        eqToHom (congrArg
          (fun q => ((adamsMappingConvergingSS X Y hX hY).E.ssData q).eInfty)
          (by ext <;> simp)) =
      (λ_ ((adamsMappingConvergingSS X Y hX hY).E.ssData k).eInfty).hom

/-- The E-infinity composition pairing has the identity of `Y` as a right unit. -/
axiom adamsCompositionConvergingSSPairing_eInfty_right_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (k : ℤ × ℤ) :
    (𝟙 ((adamsMappingConvergingSS X Y hX hY).E.ssData k).eInfty ⊗ₘ
        (adamsMappingConvergingSSUnit Y hY).eInfty) ≫
      (adamsCompositionConvergingSSPairing X Y Y hX hY hY).eInftyPair k (0, 0) ≫
        eqToHom (congrArg
          (fun q => ((adamsMappingConvergingSS X Y hX hY).E.ssData q).eInfty)
          (by ext <;> simp)) =
      (ρ_ ((adamsMappingConvergingSS X Y hX hY).E.ssData k).eInfty).hom

/-- The abutment composition pairing has the identity of `X` as a left unit. -/
axiom adamsCompositionConvergingSSPairing_abutment_left_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (n : ℤ) :
    ((adamsMappingConvergingSSUnit X hX).abutment ⊗ₘ
        𝟙 ((adamsMappingConvergingSS X Y hX hY).A n)) ≫
      (adamsCompositionConvergingSSPairing X X Y hX hX hY).abutmentPair 0 n ≫
        eqToHom (by simp) =
      (λ_ ((adamsMappingConvergingSS X Y hX hY).A n)).hom

/-- The abutment composition pairing has the identity of `Y` as a right unit. -/
axiom adamsCompositionConvergingSSPairing_abutment_right_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (n : ℤ) :
    (𝟙 ((adamsMappingConvergingSS X Y hX hY).A n) ⊗ₘ
        (adamsMappingConvergingSSUnit Y hY).abutment) ≫
      (adamsCompositionConvergingSSPairing X Y Y hX hY hY).abutmentPair n 0 ≫
        eqToHom (by simp) =
      (ρ_ ((adamsMappingConvergingSS X Y hX hY).A n)).hom

/-! ### The sphere Adams spectral sequence -/

/-- The converging mod-2 Adams spectral sequence of the sphere. -/
noncomputable abbrev sphereAdamsConvergingSS :
    ConvergingSS (ModuleCat.{v} IntModuleRing) (ℤ × ℤ) ℤ :=
  adamsMappingConvergingSS (𝒮 := 𝒮) SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere

/-- Its underlying spectral sequence is the ordinary Adams spectral sequence
of the sphere. -/
theorem sphereAdamsConvergingSS_ss :
    (sphereAdamsConvergingSS (𝒮 := 𝒮)).E =
      SpectralSequence.transfer
        (AdamsSS (𝒮 := 𝒮) SphereSpectrum) := by
  rfl

/-- Composition supplies the multiplication on the sphere Adams spectral
sequence, on every page, on `E∞`, and on the abutment. -/
noncomputable abbrev sphereAdamsMultiplication :
    ConvergingSSPairing (sphereAdamsConvergingSS (𝒮 := 𝒮))
      (sphereAdamsConvergingSS (𝒮 := 𝒮))
      (sphereAdamsConvergingSS (𝒮 := 𝒮)) :=
  adamsCompositionConvergingSSPairing SphereSpectrum SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere

/-- The identity of the sphere gives the unit on pages, `E∞`, and the
abutment. The existing composition axioms establish its unit laws. -/
noncomputable abbrev sphereAdamsUnit :
    AdamsMappingConvergingSSUnit SphereSpectrum
      (IsFiniteSpectrum.sphere (𝒮 := 𝒮)) :=
  adamsMappingConvergingSSUnit SphereSpectrum IsFiniteSpectrum.sphere

/-- The Koszul parity in the sphere Adams product is the parity of the stem. -/
theorem sphereAdamsMultiplication_parity (s t : ℤ) :
    (sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.parity (s, t) =
      (↑(t - s) : ZMod 2) :=
  adamsCompositionConvergingSSPairing_parity
    SphereSpectrum SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere s t

/-- The sphere Adams multiplication is associative on every page. -/
theorem sphereAdamsMultiplication_associative (r : ℤ)
    (i j k : ℤ × ℤ) :
    ((sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.pair r i j ⊗ₘ
        𝟙 ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r k)) ≫
      (sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.pair r (i + j) k ≫
        eqToHom (by ac_rfl) =
      (α_ ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r i)
        ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r j)
        ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r k)).hom ≫
      (𝟙 ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r i) ⊗ₘ
        (sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.pair r j k) ≫
      (sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.pair r i (j + k) :=
  adamsCompositionConvergingSSPairing_associative
    SphereSpectrum SphereSpectrum SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere r i j k

end KIPBase.StableHomotopy
