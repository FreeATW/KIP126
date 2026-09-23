/-
  KIPBase.multiplicativeSS.Basic

  Multiplicative pairings of spectral sequences. A pairing is defined on
  every page and every pair of graded pieces. Its differential obeys the
  signed Leibniz rule, and termwise page isomorphisms preserve multiplication.
-/
import KIPBase.Mathlib
import KIPBase.SpectralSequence.Basic
import KIPBase.SpectralSequence.Convergence
import KIPBase.multiplicativeSS.DGA

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- A linear parity function on a (possibly multi-)graded indexing group.
Its value is the degree modulo two. -/
abbrev GradingParity (ι : Type w) [AddCommGroup ι] := ι →+ ZMod 2

/-- A termwise isomorphism between two pages of a spectral sequence. -/
structure SSPageIso {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r s : ℤ) where
  /-- The isomorphism on the graded piece indexed by `k`. -/
  iso : ∀ k : ι, E.Page r k ≅ E.Page s k

/-- The middle term of the short complex which computes the next page at
degree `k` is canonically the current page `E_r^k`. -/
noncomputable def SpectralSequence.pageShortComplexCenterIso
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₂ ≅ E.Page r k :=
  eqToIso (by simp [SpectralSequence.pageShortComplex])

/-- A graded pairing `E₁ ⊗ E₂ → E₃` on all pages of three spectral sequences.
The three differentials are required to have the same degree.  For a
multi-index grading, `parity : ι →+ ZMod 2` chooses the linear parity used in
the Koszul sign. -/
structure SSPairing {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E₁ E₂ E₃ : SpectralSequence C ι) where
  /-- The common differential degree of the three spectral sequences. -/
  diffDeg_compatible : ∀ r : ℤ,
    E₁.diffDeg r = E₂.diffDeg r ∧ E₁.diffDeg r = E₃.diffDeg r
  /-- The linear parity convention for the grading. -/
  parity : GradingParity ι
  /-- The product on the `r`-th pages. -/
  pair : ∀ (r : ℤ) (k l : ι),
    E₁.Page r k ⊗ E₂.Page r l ⟶ E₃.Page r (k + l)
  /-- The differential satisfies the signed Leibniz rule. -/
  leibniz : ∀ (r : ℤ) (k l : ι),
    pair r k l ≫ E₃.d r (k + l) =
      (E₁.d r k ⊗ₘ 𝟙 (E₂.Page r l)) ≫ pair r (k + E₁.diffDeg r) l ≫
        eqToHom (by
          rw [(diffDeg_compatible r).2]
          ac_rfl) +
      (𝟙 (E₁.Page r k) ⊗ₘ E₂.d r l) ≫ pair r k (l + E₂.diffDeg r) ≫
        eqToHom (by
          rw [← (diffDeg_compatible r).1, (diffDeg_compatible r).2]
          ac_rfl) ≫
        if parity k = 1 then -(𝟙 (E₃.Page r (k + l + E₃.diffDeg r)))
        else 𝟙 (E₃.Page r (k + l + E₃.diffDeg r))
  /-- Product of cycles in the three page short complexes.  This is the
  categorical counterpart of `DGA.homogeneousCycleMul`. -/
  cyclePair : ∀ (r : ℤ) (k l : ι),
    (E₁.pageShortComplex r (k - E₁.diffDeg r)).cycles ⊗
        (E₂.pageShortComplex r (l - E₂.diffDeg r)).cycles ⟶
      (E₃.pageShortComplex r (k + l - E₃.diffDeg r)).cycles
  /-- The cycle product is the restriction of the product on the current
  page. -/
  cyclePair_compatible : ∀ (r : ℤ) (k l : ι),
    cyclePair r k l ≫
        (E₃.pageShortComplex r (k + l - E₃.diffDeg r)).iCycles ≫
        (E₃.pageShortComplexCenterIso r (k + l)).hom =
      (((E₁.pageShortComplex r (k - E₁.diffDeg r)).iCycles ≫
          (E₁.pageShortComplexCenterIso r k).hom) ⊗ₘ
        ((E₂.pageShortComplex r (l - E₂.diffDeg r)).iCycles ≫
          (E₂.pageShortComplexCenterIso r l).hom)) ≫
        pair r k l
  /-- Product induced on homology by `cyclePair`.  This is the categorical
  counterpart of `DGA.homologyMul`. -/
  homologyPair : ∀ (r : ℤ) (k l : ι),
    (E₁.pageShortComplex r (k - E₁.diffDeg r)).homology ⊗
        (E₂.pageShortComplex r (l - E₂.diffDeg r)).homology ⟶
      (E₃.pageShortComplex r (k + l - E₃.diffDeg r)).homology
  /-- `homologyPair` is the descent of `cyclePair` through the cycle-to-
  homology quotient maps, exactly as `DGA.homogeneousCycleMul_respects`
  supplies the descent used by `DGA.homologyMul`. -/
  homologyPair_compatible : ∀ (r : ℤ) (k l : ι),
    ((E₁.pageShortComplex r (k - E₁.diffDeg r)).homologyπ ⊗ₘ
        (E₂.pageShortComplex r (l - E₂.diffDeg r)).homologyπ) ≫
        homologyPair r k l =
      cyclePair r k l ≫
        (E₃.pageShortComplex r (k + l - E₃.diffDeg r)).homologyπ
  /-- The tensor of the two quotient maps is epic.  Consequently the
  preceding square determines `homologyPair` uniquely.  This is automatic
  for the elementwise quotient construction used by `DGA.homologyMul`; it is
  stated here because an arbitrary monoidal abelian category need not make
  tensor preserve epimorphisms. -/
  homologyPair_quotient_epi : ∀ (r : ℤ) (k l : ι),
    Epi ((E₁.pageShortComplex r (k - E₁.diffDeg r)).homologyπ ⊗ₘ
      (E₂.pageShortComplex r (l - E₂.diffDeg r)).homologyπ)
  /-- The product on `E_(r+1)` is the product induced on the homology of
  `E_r`, transported through `SpectralSequence.pageHomologyIso`.  In the
  concrete DGA model, associativity of this descended operation is proved by
  `DGA.homologyMul_assoc`, rather than assumed as extra next-page data. -/
  nextPage_compatible : ∀ (r : ℤ) (k l : ι)
      (h₁ : E₁.r₀ ≤ r) (h₂ : E₂.r₀ ≤ r) (h₃ : E₃.r₀ ≤ r),
    pair (r + 1) k l =
      ((E₁.pageHomologyIso r k h₁).hom ⊗ₘ (E₂.pageHomologyIso r l h₂).hom) ≫
        homologyPair r k l ≫ (E₃.pageHomologyIso r (k + l) h₃).inv

/-- A homology product is uniquely determined by its value on pairs of cycle
representatives, provided by the quotient-epimorphism condition in
`SSPairing`.  This rules out choosing an unrelated multiplication on the
next page after fixing `cyclePair`. -/
theorem SSPairing.homologyPair_eq_of_compatible
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E₁ E₂ E₃ : SpectralSequence C ι} (P : SSPairing E₁ E₂ E₃)
    {r : ℤ} {k l : ι}
    (f : (E₁.pageShortComplex r (k - E₁.diffDeg r)).homology ⊗
        (E₂.pageShortComplex r (l - E₂.diffDeg r)).homology ⟶
      (E₃.pageShortComplex r (k + l - E₃.diffDeg r)).homology)
    (hf :
      ((E₁.pageShortComplex r (k - E₁.diffDeg r)).homologyπ ⊗ₘ
          (E₂.pageShortComplex r (l - E₂.diffDeg r)).homologyπ) ≫ f =
        P.cyclePair r k l ≫
          (E₃.pageShortComplex r (k + l - E₃.diffDeg r)).homologyπ) :
    f = P.homologyPair r k l := by
  letI : Epi ((E₁.pageShortComplex r (k - E₁.diffDeg r)).homologyπ ⊗ₘ
      (E₂.pageShortComplex r (l - E₂.diffDeg r)).homologyπ) :=
    P.homologyPair_quotient_epi r k l
  apply (cancel_epi ((E₁.pageShortComplex r (k - E₁.diffDeg r)).homologyπ ⊗ₘ
    (E₂.pageShortComplex r (l - E₂.diffDeg r)).homologyπ)).mp
  rw [hf, P.homologyPair_compatible]

/-- A multiplicative spectral sequence is a pairing of a spectral sequence
with itself, landing back in the same spectral sequence. -/
abbrev MultiplicativeSS {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) :=
  SSPairing E E E

/-- The three cycle-to-homology quotient maps for three (not necessarily
equal) spectral sequences remain epic after left-associated tensoring. -/
def SSPageTripleQuotientEpi
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E₁ E₂ E₃ : SpectralSequence C ι) (r : ℤ) : Prop :=
  ∀ i j k : ι,
    Epi
      (((E₁.pageShortComplex r (i - E₁.diffDeg r)).homologyπ ⊗ₘ
        (E₂.pageShortComplex r (j - E₂.diffDeg r)).homologyπ) ⊗ₘ
        (E₃.pageShortComplex r (k - E₃.diffDeg r)).homologyπ)

/-- Exactness needed to descend a threefold cycle identity to homology.
For a general monoidal abelian category this is an additional hypothesis:
the binary condition in `SSPairing.homologyPair_quotient_epi` does not imply
that tensoring with a third quotient map remains epic.  It is automatic in
the elementwise quotient construction used by `DGA.homologyMul`. -/
def MultiplicativeSS.HomologyTripleQuotientEpi
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} (P : MultiplicativeSS E) (r : ℤ) : Prop :=
  SSPageTripleQuotientEpi E E E r

/-- Equality of maps out of a threefold homology tensor can be checked on
cycle representatives under `HomologyTripleQuotientEpi`. -/
theorem MultiplicativeSS.homologyTriple_ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} {P : MultiplicativeSS E} {r : ℤ}
    (hEpi : P.HomologyTripleQuotientEpi r) {i j k : ι} {Z : C}
    (f g : ((E.pageShortComplex r (i - E.diffDeg r)).homology ⊗
        (E.pageShortComplex r (j - E.diffDeg r)).homology) ⊗
        (E.pageShortComplex r (k - E.diffDeg r)).homology ⟶ Z)
    (h :
      (((E.pageShortComplex r (i - E.diffDeg r)).homologyπ ⊗ₘ
        (E.pageShortComplex r (j - E.diffDeg r)).homologyπ) ⊗ₘ
        (E.pageShortComplex r (k - E.diffDeg r)).homologyπ) ≫ f =
      (((E.pageShortComplex r (i - E.diffDeg r)).homologyπ ⊗ₘ
        (E.pageShortComplex r (j - E.diffDeg r)).homologyπ) ⊗ₘ
        (E.pageShortComplex r (k - E.diffDeg r)).homologyπ) ≫ g) :
    f = g := by
  letI := hEpi i j k
  exact (cancel_epi _).mp h

/-- Associativity of the multiplication on one page.  The final `eqToHom`
accounts for the associativity isomorphism of the grading group. -/
def MultiplicativeSS.IsAssociativeAt {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} (P : MultiplicativeSS E) (r : ℤ) : Prop :=
  ∀ i j k : ι,
    (P.pair r i j ⊗ₘ 𝟙 (E.Page r k)) ≫ P.pair r (i + j) k ≫
      eqToHom (congrArg (fun q => E.Page r q) (add_assoc i j k)) =
    (α_ (E.Page r i) (E.Page r j) (E.Page r k)).hom ≫
      (𝟙 (E.Page r i) ⊗ₘ P.pair r j k) ≫ P.pair r i (j + k)

/-! The following attempted homology-propagation development is kept out of
the active API pending completion of its dependent transport proof. -/
/-
/-- The cycle object at degree `i` in the short complex computing the next
page from `E_r`. -/
noncomputable abbrev SpectralSequence.pageCycles {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (i : ι) : C :=
  (E.pageShortComplex r (i - E.diffDeg r)).cycles

/-- The homology object at degree `i` in the short complex computing the
next page from `E_r`. -/
noncomputable abbrev SpectralSequence.pageHomology {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (i : ι) : C :=
  (E.pageShortComplex r (i - E.diffDeg r)).homology

/-- Associativity of the product restricted to cycle representatives. -/
def MultiplicativeSS.IsCycleAssociativeAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} (P : MultiplicativeSS E) (r : ℤ) : Prop :=
  ∀ i j k : ι,
    (P.cyclePair r i j ⊗ₘ 𝟙 (E.pageCycles r k)) ≫
        P.cyclePair r (i + j) k ≫
        eqToHom (congrArg (E.pageCycles r) (add_assoc i j k)) =
      (α_ (E.pageCycles r i) (E.pageCycles r j) (E.pageCycles r k)).hom ≫
        (𝟙 (E.pageCycles r i) ⊗ₘ P.cyclePair r j k) ≫
        P.cyclePair r i (j + k)

/-- Associativity of the product induced on the homology objects which form
the next page. -/
def MultiplicativeSS.IsHomologyAssociativeAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} (P : MultiplicativeSS E) (r : ℤ) : Prop :=
  ∀ i j k : ι,
    (P.homologyPair r i j ⊗ₘ 𝟙 (E.pageHomology r k)) ≫
        P.homologyPair r (i + j) k ≫
        eqToHom (congrArg (E.pageHomology r) (add_assoc i j k)) =
      (α_ (E.pageHomology r i) (E.pageHomology r j)
        (E.pageHomology r k)).hom ≫
        (𝟙 (E.pageHomology r i) ⊗ₘ P.homologyPair r j k) ≫
        P.homologyPair r i (j + k)

/-- Associativity on a page restricts to associativity on the cycle objects
of the short complexes computing its homology. -/
theorem MultiplicativeSS.isCycleAssociativeAt_of_isAssociativeAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} {P : MultiplicativeSS E} {r : ℤ}
    (hr : P.IsAssociativeAt r) : P.IsCycleAssociativeAt r := by
  intro i j k
  let inc : ∀ a : ι, E.pageCycles r a ⟶ E.Page r a := fun a =>
    (E.pageShortComplex r (a - E.diffDeg r)).iCycles ≫
      (E.pageShortComplexCenterIso r a).hom
  have hinc (a b : ι) :
      P.cyclePair r a b ≫ inc (a + b) =
        (inc a ⊗ₘ inc b) ≫ P.pair r a b :=
    P.cyclePair_compatible r a b
  have hcast :
      eqToHom (congrArg (E.pageCycles r) (add_assoc i j k)) ≫ inc (i + (j + k)) =
        inc (i + j + k) := by
    cases add_assoc i j k
    rfl
  have hinc_mono : Mono (inc (i + (j + k))) := by
    dsimp [inc]
    infer_instance
  apply (cancel_mono (inc (i + (j + k)))).mp
  rw [Category.assoc, hcast, hinc]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [hinc]
  simp only [Category.assoc]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [hinc]
  simp only [Category.assoc]
  rw [associator_naturality]
  simpa only [Category.assoc] using
    congr(((inc i ⊗ₘ inc j) ⊗ₘ inc k) ≫ $(hr i j k))

/-- Associativity on cycle representatives descends to the homology product.
The proof is the categorical form of the `Quotient.map₂` argument in
`DGA.homologyMul_assoc`: compare the two maps after the three quotient maps,
then cancel their epic tensor. -/
theorem MultiplicativeSS.isHomologyAssociativeAt_of_isCycleAssociativeAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} {P : MultiplicativeSS E} {r : ℤ}
    (hEpi : P.HomologyTripleQuotientEpi r) (hr : P.IsCycleAssociativeAt r) :
    P.IsHomologyAssociativeAt r := by
  intro i j k
  let π : ∀ a : ι, E.pageCycles r a ⟶ E.pageHomology r a := fun a =>
    (E.pageShortComplex r (a - E.diffDeg r)).homologyπ
  have hmul (a b : ι) :
      (π a ⊗ₘ π b) ≫ P.homologyPair r a b =
        P.cyclePair r a b ≫ π (a + b) :=
    P.homologyPair_compatible r a b
  have hπcast :
      π (i + j + k) ≫
          eqToHom (congrArg (E.pageHomology r) (add_assoc i j k)) =
        eqToHom (congrArg (E.pageCycles r) (add_assoc i j k)) ≫
          π (i + (j + k)) := by
    cases add_assoc i j k
    rfl
  apply P.homologyTriple_ext hEpi
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.comp_id]
  rw [hmul]
  rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [hmul, hπcast]
  simp only [Category.assoc]
  rw [associator_naturality]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [hmul]
  rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [hmul]
  simpa only [Category.assoc] using
    congr($(hr i j k) ≫ π (i + (j + k)))

/-- If the product on `E_r` is associative, then the homology-induced product
on `E_(r+1)` is associative.  Unlike the page-isomorphism lemma below, this
uses the actual `E_(r+1) = H(E_r)` construction. -/
theorem MultiplicativeSS.isAssociativeAt_succ
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} {P : MultiplicativeSS E} {r : ℤ}
    (hEpi : P.HomologyTripleQuotientEpi r) (h₀ : E.r₀ ≤ r)
    (hr : P.IsAssociativeAt r) : P.IsAssociativeAt (r + 1) := by
  have hH : P.IsHomologyAssociativeAt r :=
    P.isHomologyAssociativeAt_of_isCycleAssociativeAt hEpi
      (P.isCycleAssociativeAt_of_isAssociativeAt hr)
  let e : ∀ a : ι, E.Page (r + 1) a ≅ E.pageHomology r a := fun a =>
    E.pageHomologyIso r a h₀
  have hpair (a b : ι) :
      P.pair (r + 1) a b =
        ((e a).hom ⊗ₘ (e b).hom) ≫ P.homologyPair r a b ≫ (e (a + b)).inv :=
    P.nextPage_compatible r a b h₀ h₀ h₀
  intro i j k
  have hleft :
      ((((e i).hom ⊗ₘ (e j).hom) ≫ P.homologyPair r i j ≫
          (e (i + j)).inv) ⊗ₘ 𝟙 (E.Page (r + 1) k)) ≫
        ((e (i + j)).hom ⊗ₘ (e k).hom) =
      (((e i).hom ⊗ₘ (e j).hom) ≫ P.homologyPair r i j) ⊗ₘ (e k).hom := by
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.comp_whiskerRight]
    rw [MonoidalCategory.comp_whiskerRight (P.homologyPair r i j) (e (i + j)).inv]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerRight_comp_tensorHom]
    simp only [Iso.inv_hom_id]
    rw [MonoidalCategory.id_tensorHom]
    rw [← MonoidalCategory.comp_whiskerRight_assoc]
    rw [← MonoidalCategory.tensorHom_def]
  have hright :
      (𝟙 (E.Page (r + 1) i) ⊗ₘ
        (((e j).hom ⊗ₘ (e k).hom) ≫ P.homologyPair r j k ≫
          (e (j + k)).inv)) ≫
        ((e i).hom ⊗ₘ (e (j + k)).hom) =
      (e i).hom ⊗ₘ (((e j).hom ⊗ₘ (e k).hom) ≫ P.homologyPair r j k) := by
    rw [MonoidalCategory.id_tensorHom, MonoidalCategory.whiskerLeft_comp]
    rw [MonoidalCategory.whiskerLeft_comp (E.Page (r + 1) i)
      (P.homologyPair r j k) (e (j + k)).inv]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerLeft_comp_tensorHom]
    simp only [Iso.inv_hom_id]
    rw [MonoidalCategory.tensorHom_id]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.tensorHom_def']
  have htotal :
      (e (i + j + k)).inv ≫
        eqToHom (congrArg (fun q => E.Page (r + 1) q) (add_assoc i j k)) =
      eqToHom (congrArg (E.pageHomology r) (add_assoc i j k)) ≫
        (e (i + (j + k))).inv := by
    simpa using
      (eqToHom_iso_inv_naturality (fun q : ι => e q) (add_assoc i j k))
  have hsource :
      (((e i).hom ⊗ₘ (e j).hom) ≫ P.homologyPair r i j) ⊗ₘ (e k).hom =
      (((e i).hom ⊗ₘ (e j).hom) ⊗ₘ (e k).hom) ≫
        (P.homologyPair r i j ⊗ₘ 𝟙 (E.pageHomology r k)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  have htarget :
      (e i).hom ⊗ₘ (((e j).hom ⊗ₘ (e k).hom) ≫ P.homologyPair r j k) =
      ((e i).hom ⊗ₘ ((e j).hom ⊗ₘ (e k).hom)) ≫
        (𝟙 (E.pageHomology r i) ⊗ₘ P.homologyPair r j k) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  rw [hpair i j, hpair (i + j) k, hpair j k, hpair i (j + k)]
  simp only [Category.assoc]
  rw [← Category.assoc, hleft]
  rw [← Category.assoc, hright]
  rw [← Category.assoc, htotal]
  rw [← Category.assoc, hsource]
  rw [← Category.assoc, htarget]
  simpa only [Category.assoc, associator_naturality_assoc] using
    congr((((e i).hom ⊗ₘ (e j).hom) ⊗ₘ (e k).hom) ≫
      $(hH i j k) ≫ (e (i + (j + k))).inv)

/-- Associativity propagates through all later pages when the threefold
cycle-to-homology quotient is epic on every page.  This is the genuine
homology-based propagation theorem; no page isomorphism between distinct
finite pages is assumed. -/
theorem MultiplicativeSS.isAssociativeFrom_of_homology
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} {P : MultiplicativeSS E} {r : ℤ}
    (hEpi : ∀ s : ℤ, r ≤ s → P.HomologyTripleQuotientEpi s)
    (h₀ : E.r₀ ≤ r) (hr : P.IsAssociativeAt r) :
    ∀ s : ℤ, r ≤ s → P.IsAssociativeAt s := by
  intro s hrs
  induction s, hrs using Int.le_induction with
  | base => exact hr
  | succ s hs hAssoc =>
      exact P.isAssociativeAt_succ (hEpi s hs) (h₀.trans hs) hAssoc

-/
/-- A multiplicative spectral sequence is associative from page `r` onward
when its product is associative on every page `s ≥ r`. -/
def MultiplicativeSS.IsAssociativeFrom {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} (P : MultiplicativeSS E) (r : ℤ) : Prop :=
  ∀ s : ℤ, r ≤ s → P.IsAssociativeAt s

/-- A multiplicative spectral sequence equipped with the proof that it is
associative from page `r` onward. -/
structure AssociativeMultiplicativeSSFrom
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) where
  toMultiplicativeSS : MultiplicativeSS E
  associative_from : toMultiplicativeSS.IsAssociativeFrom r

/-- A triple of page isomorphisms preserves a pairing when applying the two
source isomorphisms before multiplication agrees with multiplying first and
then applying the target isomorphism. -/
def SSPairing.PageIsoPreserves {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E₁ E₂ E₃ : SpectralSequence C ι} (P : SSPairing E₁ E₂ E₃)
    {r s : ℤ} (e₁ : SSPageIso E₁ r s) (e₂ : SSPageIso E₂ r s)
    (e₃ : SSPageIso E₃ r s) : Prop :=
  ∀ k l : ι,
    ((e₁.iso k).hom ⊗ₘ (e₂.iso l).hom) ≫ P.pair s k l =
      P.pair r k l ≫ (e₃.iso (k + l)).hom

/-- A page isomorphism of pairings: termwise page isomorphisms for all three
spectral sequences, together with multiplicative compatibility. -/
structure SSPairing.PageIso {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E₁ E₂ E₃ : SpectralSequence C ι} (P : SSPairing E₁ E₂ E₃)
    (r s : ℤ) where
  left : SSPageIso E₁ r s
  right : SSPageIso E₂ r s
  target : SSPageIso E₃ r s
  preserves_mul : P.PageIsoPreserves left right target

/-- A termwise page isomorphism of a multiplicative spectral sequence which
preserves its self-pairing. -/
structure MultiplicativePageIso {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} (P : MultiplicativeSS E) (r s : ℤ) where
  iso : SSPageIso E r s
  preserves_mul : P.PageIsoPreserves iso iso iso

/-- Associativity transports across a multiplicative page isomorphism. -/
theorem MultiplicativePageIso.isAssociativeAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} {P : MultiplicativeSS E} {r s : ℤ}
    (e : MultiplicativePageIso P r s) (hr : P.IsAssociativeAt r) :
    P.IsAssociativeAt s := by
  have hpair (a b : ι) :
      P.pair s a b =
        ((e.iso.iso a).inv ⊗ₘ (e.iso.iso b).inv) ≫ P.pair r a b ≫
          (e.iso.iso (a + b)).hom := by
    apply (cancel_epi ((e.iso.iso a).hom ⊗ₘ (e.iso.iso b).hom)).mp
    simp only [← Category.assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
    exact e.preserves_mul a b
  intro i j k
  have hleft :
      ((((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫ P.pair r i j ≫
          (e.iso.iso (i + j)).hom) ⊗ₘ 𝟙 (E.Page s k)) ≫
        ((e.iso.iso (i + j)).inv ⊗ₘ (e.iso.iso k).inv) =
      (((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫ P.pair r i j) ⊗ₘ
        (e.iso.iso k).inv := by
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.comp_whiskerRight]
    rw [MonoidalCategory.comp_whiskerRight (P.pair r i j) (e.iso.iso (i + j)).hom]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerRight_comp_tensorHom]
    simp only [Iso.hom_inv_id]
    rw [MonoidalCategory.id_tensorHom]
    rw [← MonoidalCategory.comp_whiskerRight_assoc]
    rw [← MonoidalCategory.tensorHom_def]
  have hright :
      (𝟙 (E.Page s i) ⊗ₘ
        (((e.iso.iso j).inv ⊗ₘ (e.iso.iso k).inv) ≫ P.pair r j k ≫
          (e.iso.iso (j + k)).hom)) ≫
        ((e.iso.iso i).inv ⊗ₘ (e.iso.iso (j + k)).inv) =
      (e.iso.iso i).inv ⊗ₘ
        (((e.iso.iso j).inv ⊗ₘ (e.iso.iso k).inv) ≫ P.pair r j k) := by
    rw [MonoidalCategory.id_tensorHom, MonoidalCategory.whiskerLeft_comp]
    rw [MonoidalCategory.whiskerLeft_comp (E.Page s i) (P.pair r j k)
      (e.iso.iso (j + k)).hom]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerLeft_comp_tensorHom]
    simp only [Iso.hom_inv_id]
    rw [MonoidalCategory.tensorHom_id]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.tensorHom_def']
  have hleft_assoc {Z : C} (q : E.Page r (i + j) ⊗ E.Page r k ⟶ Z) :
      ((((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫ P.pair r i j ≫
          (e.iso.iso (i + j)).hom) ⊗ₘ 𝟙 (E.Page s k)) ≫
          ((e.iso.iso (i + j)).inv ⊗ₘ (e.iso.iso k).inv) ≫ q =
      ((((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫ P.pair r i j) ⊗ₘ
          (e.iso.iso k).inv) ≫ q := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ q) hleft
  have hright_assoc {Z : C} (q : E.Page r i ⊗ E.Page r (j + k) ⟶ Z) :
      (𝟙 (E.Page s i) ⊗ₘ
        (((e.iso.iso j).inv ⊗ₘ (e.iso.iso k).inv) ≫ P.pair r j k ≫
          (e.iso.iso (j + k)).hom)) ≫
          ((e.iso.iso i).inv ⊗ₘ (e.iso.iso (j + k)).inv) ≫ q =
      ((e.iso.iso i).inv ⊗ₘ
        (((e.iso.iso j).inv ⊗ₘ (e.iso.iso k).inv) ≫ P.pair r j k)) ≫ q := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ q) hright
  have htotal :
      (e.iso.iso (i + j + k)).hom ≫
        eqToHom (congrArg (fun q => E.Page s q) (add_assoc i j k)) =
      eqToHom (congrArg (fun q => E.Page r q) (add_assoc i j k)) ≫
        (e.iso.iso (i + (j + k))).hom := by
    simpa using
      (eqToHom_iso_hom_naturality (fun q : ι => e.iso.iso q) (add_assoc i j k))
  have hsource :
      (((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫ P.pair r i j) ⊗ₘ
        (e.iso.iso k).inv =
      (((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ⊗ₘ (e.iso.iso k).inv) ≫
        (P.pair r i j ⊗ₘ 𝟙 (E.Page r k)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  have hsource_assoc {Z : C}
      (q : E.Page r (i + j) ⊗ E.Page r k ⟶ Z) :
      ((((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫ P.pair r i j) ⊗ₘ
          (e.iso.iso k).inv) ≫ q =
      (((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ⊗ₘ (e.iso.iso k).inv) ≫
        (P.pair r i j ⊗ₘ 𝟙 (E.Page r k)) ≫ q := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ q) hsource
  have htarget :
      (e.iso.iso i).inv ⊗ₘ
        (((e.iso.iso j).inv ⊗ₘ (e.iso.iso k).inv) ≫ P.pair r j k) =
      ((e.iso.iso i).inv ⊗ₘ ((e.iso.iso j).inv ⊗ₘ (e.iso.iso k).inv)) ≫
        (𝟙 (E.Page r i) ⊗ₘ P.pair r j k) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  have htarget_assoc {Z : C}
      (q : E.Page r i ⊗ E.Page r (j + k) ⟶ Z) :
      ((e.iso.iso i).inv ⊗ₘ
          (((e.iso.iso j).inv ⊗ₘ (e.iso.iso k).inv) ≫ P.pair r j k)) ≫ q =
      ((e.iso.iso i).inv ⊗ₘ ((e.iso.iso j).inv ⊗ₘ (e.iso.iso k).inv)) ≫
        (𝟙 (E.Page r i) ⊗ₘ P.pair r j k) ≫ q := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ q) htarget
  rw [hpair i j, hpair (i + j) k, hpair j k, hpair i (j + k)]
  simp only [Category.assoc]
  rw [hleft_assoc, hright_assoc, htotal, hsource_assoc, htarget_assoc]
  simpa only [Category.assoc, associator_naturality_assoc] using
    congr((((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ⊗ₘ (e.iso.iso k).inv) ≫
      $(hr i j k) ≫ (e.iso.iso (i + (j + k))).hom)

/-- If the page isomorphisms from page `r` to every later page are
multiplicative, then associativity on page `r` holds on every later page. -/
theorem MultiplicativeSS.isAssociativeAt_all_later
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} {P : MultiplicativeSS E} {r : ℤ}
    (pageIso : ∀ s : ℤ, r ≤ s → MultiplicativePageIso P r s)
    (hr : P.IsAssociativeAt r) :
    ∀ s : ℤ, r ≤ s → P.IsAssociativeAt s := by
  intro s hrs
  exact (pageIso s hrs).isAssociativeAt hr

/-- The page-isomorphism criterion packages into associativity from page
`r` onward. -/
theorem MultiplicativeSS.isAssociativeFrom_of_pageIso
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} {P : MultiplicativeSS E} {r : ℤ}
    (pageIso : ∀ s : ℤ, r ≤ s → MultiplicativePageIso P r s)
    (hr : P.IsAssociativeAt r) :
    P.IsAssociativeFrom r :=
  P.isAssociativeAt_all_later pageIso hr

/-- Graded commutativity on one page.  The braiding exchanges the two input
factors, and the final sign is `(-1)^(|i| |j|)` for the chosen linear parity.
The `eqToHom` identifies the two equal total degrees `j + i` and `i + j`. -/
def MultiplicativeSS.IsCommutativeAt {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} [BraidedCategory C]
    (P : MultiplicativeSS E) (r : ℤ) : Prop :=
  ∀ i j : ι,
    P.pair r i j =
      (β_ (E.Page r i) (E.Page r j)).hom ≫ P.pair r j i ≫
        eqToHom (congrArg (fun q => E.Page r q) (add_comm j i)) ≫
        if P.parity i * P.parity j = 1 then -(𝟙 (E.Page r (i + j)))
        else 𝟙 (E.Page r (i + j))

/-- A multiplicative page isomorphism equipped with the braiding coherence
needed to transport graded commutativity. -/
structure MultiplicativeBraidedPageIso
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} [BraidedCategory C]
    (P : MultiplicativeSS E) (r s : ℤ) extends MultiplicativePageIso P r s where

/-- Graded commutativity transports across a multiplicative braided page
isomorphism. -/
theorem MultiplicativeBraidedPageIso.isCommutativeAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} [BraidedCategory C]
    {P : MultiplicativeSS E} {r s : ℤ}
    (e : MultiplicativeBraidedPageIso P r s) (hr : P.IsCommutativeAt r) :
    P.IsCommutativeAt s := by
  have hpair (a b : ι) :
      P.pair s a b =
        ((e.iso.iso a).inv ⊗ₘ (e.iso.iso b).inv) ≫ P.pair r a b ≫
          (e.iso.iso (a + b)).hom := by
    apply (cancel_epi ((e.iso.iso a).hom ⊗ₘ (e.iso.iso b).hom)).mp
    simp only [← Category.assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
    exact e.preserves_mul a b
  intro i j
  have hbraid :
      (β_ (E.Page s i) (E.Page s j)).hom ≫
        ((e.iso.iso j).inv ⊗ₘ (e.iso.iso i).inv) =
      ((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫
        (β_ (E.Page r i) (E.Page r j)).hom := by
    simpa using
      (BraidedCategory.braiding_naturality (e.iso.iso i).inv (e.iso.iso j).inv).symm
  have hbraid_assoc {Z : C}
      (q : E.Page r j ⊗ E.Page r i ⟶ Z) :
      (β_ (E.Page s i) (E.Page s j)).hom ≫
          ((e.iso.iso j).inv ⊗ₘ (e.iso.iso i).inv) ≫ q =
      ((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫
          (β_ (E.Page r i) (E.Page r j)).hom ≫ q := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ q) hbraid
  have htotal :
      (e.iso.iso (j + i)).hom ≫
        eqToHom (congrArg (fun q => E.Page s q) (add_comm j i)) =
      eqToHom (congrArg (fun q => E.Page r q) (add_comm j i)) ≫
        (e.iso.iso (i + j)).hom := by
    simpa using
      (eqToHom_iso_hom_naturality (fun q : ι => e.iso.iso q) (add_comm j i))
  have htotal_assoc {Z : C}
      (q : E.Page s (i + j) ⟶ Z) :
      (e.iso.iso (j + i)).hom ≫
          eqToHom (congrArg (fun q => E.Page s q) (add_comm j i)) ≫ q =
      eqToHom (congrArg (fun q => E.Page r q) (add_comm j i)) ≫
        (e.iso.iso (i + j)).hom ≫ q := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ q) htotal
  have hsign :
      (e.iso.iso (i + j)).hom ≫
        (if P.parity i * P.parity j = 1 then -(𝟙 (E.Page s (i + j)))
        else 𝟙 (E.Page s (i + j))) =
      (if P.parity i * P.parity j = 1 then -(𝟙 (E.Page r (i + j)))
        else 𝟙 (E.Page r (i + j))) ≫
        (e.iso.iso (i + j)).hom := by
    split <;> simp only [Category.comp_id, Category.id_comp, Preadditive.comp_neg,
      Preadditive.neg_comp]
  rw [hpair i j, hpair j i]
  simp only [Category.assoc]
  rw [hbraid_assoc, htotal_assoc, hsign]
  simpa only [Category.assoc] using
    congr(((e.iso.iso i).inv ⊗ₘ (e.iso.iso j).inv) ≫ $(hr i j) ≫
      (e.iso.iso (i + j)).hom)

/-- If the page isomorphisms from page `r` to every later page preserve the
braiding and multiplication, then commutativity on page `r` holds later. -/
theorem MultiplicativeSS.isCommutativeAt_all_later
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence C ι} [BraidedCategory C]
    {P : MultiplicativeSS E} {r : ℤ}
    (pageIso : ∀ s : ℤ, r ≤ s → MultiplicativeBraidedPageIso P r s)
    (hr : P.IsCommutativeAt r) :
    ∀ s : ℤ, r ≤ s → P.IsCommutativeAt s := by
  intro s hrs
  exact (pageIso s hrs).isCommutativeAt hr

/-! ### Pairings of converging spectral sequences -/

/-- A pairing of three converging spectral sequences.  In addition to the
pagewise pairing, it records products on the `E∞` pages and on the abutment.
The abutment product is required to preserve the filtrations, and its induced
product on the associated graded is required to be the recorded
`associatedGradedPair`. -/
structure ConvergingSSPairing
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    (X₁ X₂ X₃ : ConvergingSS C ω ω') where
  /-- The product on every page of the underlying spectral sequences. -/
  ssPairing : SSPairing X₁.E X₂.E X₃.E
  /-- The product on the E-infinity pages. -/
  eInftyPair : ∀ k l : ω,
    (X₁.E.ssData k).eInfty ⊗ (X₂.E.ssData l).eInfty ⟶
      (X₃.E.ssData (k + l)).eInfty
  /-- One product on representatives that remain cycles at every page. -/
  cyclePairAtInfinity : ∀ k l : ω,
    Subobject.underlying.obj ((X₁.E.ssData k).Z ⊤) ⊗
      Subobject.underlying.obj ((X₂.E.ssData l).Z ⊤) ⟶
      Subobject.underlying.obj ((X₃.E.ssData (k + l)).Z ⊤)
  /-- The product on `E∞` is induced by the permanent-cycle product. -/
  eInftyPair_induced : ∀ k l : ω,
    cyclePairAtInfinity k l ≫ (X₃.E.ssData (k + l)).pageπ ⊤ =
      (((X₁.E.ssData k).pageπ ⊤) ⊗ₘ
        ((X₂.E.ssData l).pageπ ⊤)) ≫ eInftyPair k l
  /-- The same permanent-cycle product restricts to the product on every
  finite page, so the finite-page and `E∞` products cannot be independent. -/
  finitePagePair_compatible : ∀ (r : ℤ) (k l : ω)
      (_h₁ : X₁.E.r₀ ≤ r) (_h₂ : X₂.E.r₀ ≤ r)
      (_h₃ : X₃.E.r₀ ≤ r),
      ((Subobject.ofLE _ _ ((X₁.E.ssData k).Z_anti le_top) ≫
            (X₁.E.ssData k).pageπ ↑(r - X₁.E.r₀).toNat) ⊗ₘ
          (Subobject.ofLE _ _ ((X₂.E.ssData l).Z_anti le_top) ≫
            (X₂.E.ssData l).pageπ ↑(r - X₂.E.r₀).toNat)) ≫
          ssPairing.pair r k l =
        cyclePairAtInfinity k l ≫
          Subobject.ofLE _ _ ((X₃.E.ssData (k + l)).Z_anti le_top) ≫
          (X₃.E.ssData (k + l)).pageπ ↑(r - X₃.E.r₀).toNat
  /-- The product on the graded abutment objects. -/
  abutmentPair : ∀ i j : ω', X₁.A i ⊗ X₂.A j ⟶ X₃.A (i + j)
  /-- The abutment product restricted to the filtration pieces.  Its existence
  expresses `F^s A_i · F^t B_j ⊆ F^(s+t) C_(i+j)`. -/
  filteredAbutmentPair : ∀ (s t : ℤ) (i j : ω'),
    Subobject.underlying.obj (X₁.F.F s i) ⊗
        Subobject.underlying.obj (X₂.F.F t j) ⟶
      Subobject.underlying.obj (X₃.F.F (s + t) (i + j))
  /-- The filtered product lifts the abutment product along the inclusions of
  filtration pieces. -/
  filteredAbutmentPair_compatible : ∀ (s t : ℤ) (i j : ω'),
    filteredAbutmentPair s t i j ≫ (X₃.F.F (s + t) (i + j)).arrow =
      ((X₁.F.F s i).arrow ⊗ₘ (X₂.F.F t j).arrow) ≫ abutmentPair i j
  /-- The product on associated graded pieces of the abutment filtrations. -/
  associatedGradedPair : ∀ (s t : ℤ) (i j : ω'),
    X₁.F.associatedGraded s i ⊗ X₂.F.associatedGraded t j ⟶
      X₃.F.associatedGraded (s + t) (i + j)
  /-- The associated-graded product is induced by the filtered abutment
  product, via the quotient maps defining the associated graded pieces. -/
  associatedGradedPair_induced : ∀ (s t : ℤ) (i j : ω'),
    (X₁.F.toAssociatedGraded s i ⊗ₘ X₂.F.toAssociatedGraded t j) ≫
        associatedGradedPair s t i j =
      filteredAbutmentPair s t i j ≫
        X₃.F.toAssociatedGraded (s + t) (i + j)
  /-- The convergence reindexings respect the additive gradings. -/
  reindex_compatible : ∀ k l : ω,
    X₁.conv.reindex k + X₂.conv.reindex l = X₃.conv.reindex (k + l)
  /-- E-infinity multiplication agrees, via convergence, with multiplication
  on associated graded abutment pieces. -/
  eInfty_compatible : ∀ k l : ω,
    eInftyPair k l ≫ (X₃.conv.iso (k + l)).hom ≫
        X₃.F.transportGraded (reindex_compatible k l).symm =
      ((X₁.conv.iso k).hom ⊗ₘ (X₂.conv.iso l).hom) ≫
        associatedGradedPair (X₁.conv.reindex k).1 (X₂.conv.reindex l).1
          (X₁.conv.reindex k).2 (X₂.conv.reindex l).2

/-- A multiplicative converging spectral sequence is a self-pairing of a
converging spectral sequence, compatible with the product on its E-infinity
page and on its filtered abutment. -/
abbrev MultiplicativeConvergingSS
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    (X : ConvergingSS C ω ω') :=
  ConvergingSSPairing X X X

/-- Associativity of a multiplicative converging spectral sequence on page
`r`. The multiplication is the underlying pagewise multiplication; its
compatibility with the abutment associated graded is already part of
`ConvergingSSPairing.eInfty_compatible`. -/
abbrev MultiplicativeConvergingSS.IsAssociativeAt
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} (P : MultiplicativeConvergingSS X) (r : ℤ) : Prop :=
  MultiplicativeSS.IsAssociativeAt P.ssPairing r

/-- Associativity of the multiplication recorded on the `E∞` page. -/
def MultiplicativeConvergingSS.IsEInftyAssociative
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} (P : MultiplicativeConvergingSS X) : Prop :=
  ∀ i j k : ω,
    (P.eInftyPair i j ⊗ₘ 𝟙 ((X.E.ssData k).eInfty)) ≫
        P.eInftyPair (i + j) k ≫
        eqToHom (congrArg (fun q => (X.E.ssData q).eInfty) (add_assoc i j k)) =
      (α_ ((X.E.ssData i).eInfty) ((X.E.ssData j).eInfty)
        ((X.E.ssData k).eInfty)).hom ≫
        (𝟙 ((X.E.ssData i).eInfty) ⊗ₘ P.eInftyPair j k) ≫
        P.eInftyPair i (j + k)

/-- Associativity of the multiplication on the graded abutment. -/
def MultiplicativeConvergingSS.IsAbutmentAssociative
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} (P : MultiplicativeConvergingSS X) : Prop :=
  ∀ i j k : ω',
    (P.abutmentPair i j ⊗ₘ 𝟙 (X.A k)) ≫
        P.abutmentPair (i + j) k ≫
        eqToHom (congrArg X.A (add_assoc i j k)) =
      (α_ (X.A i) (X.A j) (X.A k)).hom ≫
        (𝟙 (X.A i) ⊗ₘ P.abutmentPair j k) ≫ P.abutmentPair i (j + k)

/-- Associativity from page `r` for a converging multiplicative spectral
sequence means associativity on every finite page from `r`, on `E∞`, and on
the abutment.  The last two clauses cannot be inferred merely from finite-page
isomorphisms under the project's weak-convergence convention. -/
def MultiplicativeConvergingSS.IsAssociativeFrom
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} (P : MultiplicativeConvergingSS X) (r : ℤ) : Prop :=
  MultiplicativeSS.IsAssociativeFrom P.ssPairing r ∧
    P.IsEInftyAssociative ∧ P.IsAbutmentAssociative

/-- A multiplicative converging spectral sequence with associativity from
page `r` onward. -/
structure AssociativeMultiplicativeConvergingSSFrom
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    (X : ConvergingSS C ω ω') (r : ℤ) where
  toMultiplicativeConvergingSS : MultiplicativeConvergingSS X
  associative_from : toMultiplicativeConvergingSS.IsAssociativeFrom r

/-- A multiplicative page isomorphism for a converging spectral sequence.
Its E-infinity and abutment products remain compatible by the pairing data. -/
structure MultiplicativeConvergingPageIso
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} (P : MultiplicativeConvergingSS X) (r s : ℤ) where
  pageIso : MultiplicativePageIso P.ssPairing r s

/-- Associativity transports across a multiplicative converging page
isomorphism. -/
theorem MultiplicativeConvergingPageIso.isAssociativeAt
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} {P : MultiplicativeConvergingSS X} {r s : ℤ}
    (e : MultiplicativeConvergingPageIso P r s) (hr : P.IsAssociativeAt r) :
    P.IsAssociativeAt s :=
  e.pageIso.isAssociativeAt hr

/-- Associativity on page `r` propagates to every later finite page when
supplied with multiplicative page isomorphisms. -/
theorem MultiplicativeConvergingSS.isAssociativeAt_all_later
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} {P : MultiplicativeConvergingSS X} {r : ℤ}
    (pageIso : ∀ s : ℤ, r ≤ s → MultiplicativeConvergingPageIso P r s)
    (hr : P.IsAssociativeAt r) :
    ∀ s : ℤ, r ≤ s → P.IsAssociativeAt s := by
  intro s hrs
  exact (pageIso s hrs).isAssociativeAt hr

/-- Finite-page isomorphisms propagate the finite-page component of
converging associativity.  Associativity of the separately recorded `E∞` and
abutment multiplications is supplied explicitly, since weak convergence does
not identify either object with a particular finite page. -/
theorem MultiplicativeConvergingSS.isAssociativeFrom_of_pageIso
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} {P : MultiplicativeConvergingSS X} {r : ℤ}
    (pageIso : ∀ s : ℤ, r ≤ s → MultiplicativeConvergingPageIso P r s)
    (hr : P.IsAssociativeAt r) (hEInfty : P.IsEInftyAssociative)
    (hAbutment : P.IsAbutmentAssociative) :
    P.IsAssociativeFrom r :=
  ⟨MultiplicativeSS.isAssociativeAt_all_later (P := P.ssPairing)
      (fun s hs => (pageIso s hs).pageIso) hr,
    hEInfty, hAbutment⟩

/-
/-- The homology-based propagation theorem for a converging multiplicative
spectral sequence.  The finite-page component is obtained from
`E_(s+1) = H(E_s)`; the independently recorded `E∞` and abutment laws are
retained under weak convergence. -/
theorem MultiplicativeConvergingSS.isAssociativeFrom_of_homology
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} {P : MultiplicativeConvergingSS X} {r : ℤ}
    (hEpi : ∀ s : ℤ, r ≤ s → P.ssPairing.HomologyTripleQuotientEpi s)
    (h₀ : X.E.r₀ ≤ r) (hr : P.IsAssociativeAt r)
    (hEInfty : P.IsEInftyAssociative) (hAbutment : P.IsAbutmentAssociative) :
    P.IsAssociativeFrom r :=
  ⟨P.ssPairing.isAssociativeFrom_of_homology hEpi h₀ hr, hEInfty, hAbutment⟩
-/

/-- Graded commutativity on a page of a multiplicative converging spectral
sequence. The Koszul sign is inherited from its linear parity function. -/
abbrev MultiplicativeConvergingSS.IsCommutativeAt
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} [BraidedCategory C]
    (P : MultiplicativeConvergingSS X) (r : ℤ) : Prop :=
  MultiplicativeSS.IsCommutativeAt P.ssPairing r

/-- Graded commutativity of the multiplication recorded on `E∞`. -/
def MultiplicativeConvergingSS.IsEInftyCommutative
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} [BraidedCategory C]
    (P : MultiplicativeConvergingSS X) : Prop :=
  ∀ i j : ω,
    P.eInftyPair i j =
      (β_ ((X.E.ssData i).eInfty) ((X.E.ssData j).eInfty)).hom ≫
        P.eInftyPair j i ≫
        eqToHom (congrArg (fun q => (X.E.ssData q).eInfty) (add_comm j i)) ≫
        if P.ssPairing.parity i * P.ssPairing.parity j = 1 then
          -(𝟙 ((X.E.ssData (i + j)).eInfty))
        else 𝟙 ((X.E.ssData (i + j)).eInfty)

/-- Graded commutativity of the multiplication on the abutment.  The parity
is transported from the spectral-sequence grading through convergence; a
concrete theory may impose a different abutment parity by recording the
corresponding equality of parity functions. -/
def MultiplicativeConvergingSS.IsAbutmentCommutative
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} [BraidedCategory C]
    (P : MultiplicativeConvergingSS X) (parity' : GradingParity ω') : Prop :=
  ∀ i j : ω',
    P.abutmentPair i j =
      (β_ (X.A i) (X.A j)).hom ≫ P.abutmentPair j i ≫
        eqToHom (congrArg X.A (add_comm j i)) ≫
        if parity' i * parity' j = 1 then -(𝟙 (X.A (i + j)))
        else 𝟙 (X.A (i + j))

/-- Full graded commutativity from page `r`: all finite pages, `E∞`, and the
abutment.  The abutment is allowed its own linear parity because convergence
may reindex the grading. -/
def MultiplicativeConvergingSS.IsCommutativeFrom
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} [BraidedCategory C]
    (P : MultiplicativeConvergingSS X) (r : ℤ) (parity' : GradingParity ω') : Prop :=
  (∀ s : ℤ, r ≤ s → P.IsCommutativeAt s) ∧ P.IsEInftyCommutative ∧
    P.IsAbutmentCommutative parity'

/-- Braided multiplicative page isomorphism for a converging spectral
sequence. -/
structure MultiplicativeConvergingBraidedPageIso
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} [BraidedCategory C]
    (P : MultiplicativeConvergingSS X) (r s : ℤ) where
  pageIso : MultiplicativeBraidedPageIso P.ssPairing r s

/-- Graded commutativity transports across a braided multiplicative
converging page isomorphism. -/
theorem MultiplicativeConvergingBraidedPageIso.isCommutativeAt
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} [BraidedCategory C]
    {P : MultiplicativeConvergingSS X} {r s : ℤ}
    (e : MultiplicativeConvergingBraidedPageIso P r s) (hr : P.IsCommutativeAt r) :
    P.IsCommutativeAt s :=
  e.pageIso.isCommutativeAt hr

/-- Graded commutativity on page `r` propagates to every later page when
supplied with multiplicative braided page isomorphisms. -/
theorem MultiplicativeConvergingSS.isCommutativeAt_all_later
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} [BraidedCategory C]
    {P : MultiplicativeConvergingSS X} {r : ℤ}
    (pageIso : ∀ s : ℤ, r ≤ s → MultiplicativeConvergingBraidedPageIso P r s)
    (hr : P.IsCommutativeAt r) :
    ∀ s : ℤ, r ≤ s → P.IsCommutativeAt s := by
  intro s hrs
  exact (pageIso s hrs).isCommutativeAt hr

/-- Finite-page braided isomorphisms propagate the finite-page component of
commutativity.  As for associativity, `E∞` and abutment commutativity are
separate data under weak convergence and are retained as hypotheses. -/
theorem MultiplicativeConvergingSS.isCommutativeFrom_of_pageIso
    {ω ω' : Type w} [AddCommGroup ω] [DecidableEq ω] [AddCommGroup ω']
    {X : ConvergingSS C ω ω'} [BraidedCategory C]
    {P : MultiplicativeConvergingSS X} {r : ℤ} (parity' : GradingParity ω')
    (pageIso : ∀ s : ℤ, r ≤ s → MultiplicativeConvergingBraidedPageIso P r s)
    (hr : P.IsCommutativeAt r) (hEInfty : P.IsEInftyCommutative)
    (hAbutment : P.IsAbutmentCommutative parity') :
    P.IsCommutativeFrom r parity' :=
  ⟨MultiplicativeSS.isCommutativeAt_all_later (P := P.ssPairing)
      (fun s hs => (pageIso s hs).pageIso) hr,
    hEInfty, hAbutment⟩

end KIPBase.SpectralSequence
