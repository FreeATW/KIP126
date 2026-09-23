/-
Copyright (c) 2026 KIP126 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KIP126 contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.Tactic.Abel

/-!
# Nested-subobject spectral-sequence data

This is the axiom-free KIP126 migration of the data declarations in
`KIPBase/SpectralSequence/Basic.lean`.  It deliberately does not import the
historical `KIPBase` library or Mathlib's spectral-sequence structure.

At each grading, `SSData` records the classical nested chain

`V ⩾ Z₀ ⩾ Z₁ ⩾ ⋯ ⩾ Z∞ ⩾ B∞ ⩾ ⋯ ⩾ B₁ ⩾ B₀`,

and defines `E_r = Z_r / B_r`.  This file contains data and operations only;
predicates and named proofs live in the adjacent layers.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

/-- Nested cycle and boundary subobjects at one grading of a spectral sequence. -/
structure SSData (C : Type u) [Category.{v} C] [Abelian C] where
  /-- Ambient object. -/
  V : C
  /-- The decreasing family of cycle subobjects. -/
  Z : WithTop ℕ → Subobject V
  /-- The increasing family of boundary subobjects. -/
  B : WithTop ℕ → Subobject V
  /-- Cycles decrease with the page. -/
  Z_anti : Antitone Z
  /-- Boundaries increase with the page. -/
  B_mono : Monotone B
  /-- Every element is a zero-cycle. -/
  Z_zero : Z 0 = ⊤
  /-- Boundaries are cycles on every page. -/
  B_le_Z : ∀ r, B r ≤ Z r
  /-- `Z ⊤` is the infimum of the finite cycle stages. -/
  Z_top_greatest : ∀ (X : Subobject V), (∀ i : ℕ, X ≤ Z ↑i) → X ≤ Z ⊤
  /-- `B ⊤` is the supremum of the finite boundary stages. -/
  B_top_least : ∀ (X : Subobject V), (∀ i : ℕ, B ↑i ≤ X) → B ⊤ ≤ X

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The page `E_r = Z_r / B_r`. -/
noncomputable def SSData.page (D : SSData C) (r : WithTop ℕ) : C :=
  cokernel (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r))

/-- The infinity page `Z_∞ / B_∞`. -/
noncomputable def SSData.eInfty (D : SSData C) : C := D.page ⊤

/-- The quotient projection `Z_r ⟶ E_r`. -/
noncomputable def SSData.pageπ (D : SSData C) (r : WithTop ℕ) :
    Subobject.underlying.obj (D.Z r) ⟶ D.page r :=
  cokernel.π (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r))

/-- A graded complex in an abelian category with a fixed differential degree. -/
structure GradedComplex (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] where
  /-- Graded object. -/
  obj : ι → C
  /-- Degree of the differential. -/
  d_deg : ι
  /-- Differential. -/
  d : (k : ι) → obj k ⟶ obj (k + d_deg)
  /-- The differential squares to zero. -/
  d_sq : ∀ k, d k ≫ d (k + d_deg) = 0

/-- The short complex centered at grading `k`. -/
noncomputable def GradedComplex.shortComplex
    {ι : Type w} [AddCommGroup ι]
    (G : GradedComplex C ι) (k : ι) : ShortComplex C :=
  { X₁ := G.obj (k - G.d_deg)
    X₂ := G.obj k
    X₃ := G.obj (k + G.d_deg)
    f := G.d (k - G.d_deg) ≫ eqToHom (show G.obj (k - G.d_deg + G.d_deg) = G.obj k by
      congr 1
      abel)
    g := G.d k
    zero := by
      simp only [Category.assoc]
      have key : eqToHom (show G.obj (k - G.d_deg + G.d_deg) = G.obj k by
          congr 1
          abel) ≫ G.d k =
        G.d (k - G.d_deg + G.d_deg) ≫ eqToHom
          (show G.obj (k - G.d_deg + G.d_deg + G.d_deg) = G.obj (k + G.d_deg) by
            congr 1
            abel) := by
        rw [eqToHom_comp_iff]
        simp
      rw [key, ← Category.assoc, G.d_sq, zero_comp] }

/-- Homology of a graded complex at grading `k`. -/
noncomputable def GradedComplex.homology
    {ι : Type w} [AddCommGroup ι]
    (G : GradedComplex C ι) (k : ι) : C :=
  (G.shortComplex k).homology

/-- The data-only part of a spectral sequence. -/
structure PreSS (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- First displayed page. -/
  r₀ : ℤ
  /-- Nested-subobject data at each grading. -/
  ssData : ι → SSData C
  /-- Degree of the differential on each page. -/
  diffDeg : ℤ → ι
  /-- Page differential. -/
  d : (r : ℤ) → (k : ι) →
    ((ssData k).page ↑(r - r₀).toNat ⟶
      (ssData (k + diffDeg r)).page ↑(r - r₀).toNat)

/-- The page object derived from a `PreSS`. -/
@[reducible] noncomputable def PreSS.Page
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : PreSS C ι) (r : ℤ) (k : ι) : C :=
  (E.ssData k).page ↑(r - E.r₀).toNat

/-- A bare family of maps between the ambient objects of two `SSData` families. -/
structure UnderlyingMorphism
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) where
  /-- Map on each ambient object. -/
  φ : ∀ (k : ι), (D k).V ⟶ (D' k).V

/-- A morphism preserving the cycle and boundary towers. -/
structure SSDataMorphism
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) extends UnderlyingMorphism ι D D' where
  /-- The ambient maps preserve cycles. -/
  preserves_Z : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((D k).Z r) ⟶
      Subobject.underlying.obj ((D' k).Z r)),
      lift ≫ ((D' k).Z r).arrow = ((D k).Z r).arrow ≫ φ k
  /-- The ambient maps preserve boundaries. -/
  preserves_B : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((D k).B r) ⟶
      Subobject.underlying.obj ((D' k).B r)),
      lift ≫ ((D' k).B r).arrow = ((D k).B r).arrow ≫ φ k

/-- Forget the preservation witnesses of an `SSDataMorphism`. -/
def SSDataMorphism.toUnderlying
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f : SSDataMorphism ι D D') :
    UnderlyingMorphism ι D D' where
  φ := f.φ

/-- A morphism of pre-spectral sequences. -/
structure PreSSMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : PreSS C ι) extends SSDataMorphism ι E.ssData E'.ssData where
  /-- The induced maps on pages commute with the differentials. -/
  comm_d : ∀ (r : ℤ) (k : ι),
    ∃ (f_page_k : E.Page r k ⟶ E'.Page r k)
      (f_page_kd : E.Page r (k + E.diffDeg r) ⟶ E'.Page r (k + E'.diffDeg r)),
      f_page_k ≫ E'.d r k = E.d r k ≫ f_page_kd

/-- Forget differential compatibility from a `PreSSMorphism`. -/
def PreSSMorphism.ssDataMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : PreSS C ι} (f : PreSSMorphism E E') :
    SSDataMorphism ι E.ssData E'.ssData where
  φ := f.φ
  preserves_Z := f.preserves_Z
  preserves_B := f.preserves_B

/-- A nested-subobject spectral sequence. -/
structure SpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] extends PreSS C ι where
  /-- Every page differential squares to zero. -/
  d_comp_d : ∀ (r : ℤ) (k : ι), d r k ≫ d r (k + diffDeg r) = 0
  /-- The kernel of `d_r` is the image of `Z_(r+1)` on page `r`. -/
  Z_succ : ∀ (r : ℤ) (k : ι) (_ : r₀ ≤ r),
    let n := (r - r₀).toNat
    kernelSubobject (d r k) =
      imageSubobject (Subobject.ofLE
        ((ssData k).Z ↑(n + 1)) ((ssData k).Z ↑n)
        ((ssData k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (ssData k).pageπ ↑n)
  /-- The image of `d_r` is the image of `B_(r+1)` on page `r`. -/
  B_succ : ∀ (r : ℤ) (k : ι) (_ : r₀ ≤ r),
    let n := (r - r₀).toNat
    imageSubobject (d r k) =
      imageSubobject (Subobject.ofLE
        ((ssData (k + diffDeg r)).B ↑(n + 1))
        ((ssData (k + diffDeg r)).Z ↑n)
        (le_trans ((ssData (k + diffDeg r)).B_le_Z ↑(n + 1))
          ((ssData (k + diffDeg r)).Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
        (ssData (k + diffDeg r)).pageπ ↑n)

/-- Assemble a spectral sequence from its data and explicit compatibility proofs. -/
noncomputable def SpectralSequence.ofPreSS
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (P : PreSS C ι)
    (d_comp_d : ∀ (r : ℤ) (k : ι),
      P.d r k ≫ P.d r (k + P.diffDeg r) = 0)
    (Z_succ : ∀ (r : ℤ) (k : ι) (_ : P.r₀ ≤ r),
      let n := (r - P.r₀).toNat
      kernelSubobject (P.d r k) =
        imageSubobject (Subobject.ofLE
          ((P.ssData k).Z ↑(n + 1)) ((P.ssData k).Z ↑n)
          ((P.ssData k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
          (P.ssData k).pageπ ↑n))
    (B_succ : ∀ (r : ℤ) (k : ι) (_ : P.r₀ ≤ r),
      let n := (r - P.r₀).toNat
      imageSubobject (P.d r k) =
        imageSubobject (Subobject.ofLE
          ((P.ssData (k + P.diffDeg r)).B ↑(n + 1))
          ((P.ssData (k + P.diffDeg r)).Z ↑n)
          (le_trans ((P.ssData (k + P.diffDeg r)).B_le_Z ↑(n + 1))
            ((P.ssData (k + P.diffDeg r)).Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
          (P.ssData (k + P.diffDeg r)).pageπ ↑n)) :
    SpectralSequence C ι where
  toPreSS := P
  d_comp_d := d_comp_d
  Z_succ := Z_succ
  B_succ := B_succ

/-- The page object derived from a spectral sequence. -/
@[reducible] noncomputable def SpectralSequence.Page
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : C :=
  (E.ssData k).page ↑(r - E.r₀).toNat

/-- A page as a graded object. -/
noncomputable def SpectralSequence.pageGraded
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) : GradedObject ι C :=
  E.Page r

/-- The canonical quotient map `R/P ⟶ R/Q` for `P ≤ Q ≤ R`. -/
noncomputable def Subobject.cokernelDesc_ofLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P R hPR) ⟶ cokernel (Subobject.ofLE Q R hQR) :=
  cokernel.desc _ (cokernel.π (Subobject.ofLE Q R hQR)) (by
    have : Subobject.ofLE P R hPR =
        Subobject.ofLE P Q hPQ ≫ Subobject.ofLE Q R hQR :=
      (Subobject.ofLE_comp_ofLE P Q R hPQ hQR).symm
    rw [this, Category.assoc, cokernel.condition, comp_zero])

/-- The canonical map `Q/P ⟶ R/P` for `P ≤ Q ≤ R`. -/
noncomputable def Subobject.cokernelMap_ofLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P Q hPQ) ⟶ cokernel (Subobject.ofLE P R hPR) :=
  cokernel.desc _
    (Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR)) (by
      rw [← Category.assoc, Subobject.ofLE_comp_ofLE, cokernel.condition])

/-- The third-isomorphism identification `(R/P)/(Q/P) ≅ R/Q`. -/
noncomputable def Subobject.thirdIso {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR) ≅
      cokernel (Subobject.ofLE Q R hQR) :=
  { hom := cokernel.desc _ (Subobject.cokernelDesc_ofLE P Q R hPQ hQR hPR) (by
      ext
      simp only [Subobject.cokernelMap_ofLE, Subobject.cokernelDesc_ofLE,
        cokernel.π_desc_assoc, comp_zero]
      rw [Category.assoc, cokernel.π_desc, cokernel.condition])
    inv := cokernel.desc _ (cokernel.π (Subobject.ofLE P R hPR) ≫
        cokernel.π (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR)) (by
      set f := Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR
      have h1 : cokernel.π (Subobject.ofLE P Q hPQ) ≫ f =
          Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) :=
        cokernel.π_desc _ _ _
      calc
        Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) ≫ cokernel.π f =
            (Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR)) ≫
              cokernel.π f := by rw [Category.assoc]
        _ = (cokernel.π (Subobject.ofLE P Q hPQ) ≫ f) ≫ cokernel.π f := by rw [h1]
        _ = cokernel.π (Subobject.ofLE P Q hPQ) ≫ (f ≫ cokernel.π f) := by
          rw [Category.assoc]
        _ = cokernel.π (Subobject.ofLE P Q hPQ) ≫ 0 := by rw [cokernel.condition]
        _ = 0 := comp_zero)
    hom_inv_id := by
      ext
      simp only [Category.comp_id, cokernel.π_desc,
        Subobject.cokernelDesc_ofLE, cokernel.π_desc_assoc]
    inv_hom_id := by
      ext
      simp only [Category.comp_id, Category.assoc, cokernel.π_desc_assoc,
        Subobject.cokernelDesc_ofLE, cokernel.π_desc] }

/-- The short complex centered at grading `k + diffDeg r` on page `r`. -/
noncomputable def SpectralSequence.pageShortComplex
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : ShortComplex C :=
  ShortComplex.mk (E.d r k) (E.d r (k + E.diffDeg r)) (E.d_comp_d r k)

/-- A morphism of spectral sequences. -/
structure SpectralSequenceMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : SpectralSequence C ι) where
  /-- Map on each ambient object. -/
  φ : ∀ (k : ι), (E.ssData k).V ⟶ (E'.ssData k).V
  /-- The maps preserve cycles. -/
  preserves_Z : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((E.ssData k).Z r) ⟶
      Subobject.underlying.obj ((E'.ssData k).Z r)),
      lift ≫ ((E'.ssData k).Z r).arrow = ((E.ssData k).Z r).arrow ≫ φ k
  /-- The maps preserve boundaries. -/
  preserves_B : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((E.ssData k).B r) ⟶
      Subobject.underlying.obj ((E'.ssData k).B r)),
      lift ≫ ((E'.ssData k).B r).arrow = ((E.ssData k).B r).arrow ≫ φ k
  /-- The induced page maps commute with the differentials. -/
  comm_d : ∀ (r : ℤ) (k : ι),
    ∃ (f_page_k : E.Page r k ⟶ E'.Page r k)
      (f_page_kd : E.Page r (k + E.diffDeg r) ⟶
        E'.Page r (k + E'.diffDeg r)),
      f_page_k ≫ E'.d r k = E.d r k ≫ f_page_kd

/-- The map induced by a spectral-sequence morphism on the infinity page. -/
noncomputable def SpectralSequenceMorphism.eInftyMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (f : SpectralSequenceMorphism E E') (k : ι) :
    (E.ssData k).eInfty ⟶ (E'.ssData k).eInfty := by
  unfold SSData.eInfty SSData.page
  exact cokernel.map
    (Subobject.ofLE ((E.ssData k).B ⊤) ((E.ssData k).Z ⊤) ((E.ssData k).B_le_Z ⊤))
    (Subobject.ofLE ((E'.ssData k).B ⊤) ((E'.ssData k).Z ⊤) ((E'.ssData k).B_le_Z ⊤))
    (f.preserves_B k ⊤).choose
    (f.preserves_Z k ⊤).choose
    (by
      have hB := (f.preserves_B k ⊤).choose_spec
      have hZ := (f.preserves_Z k ⊤).choose_spec
      apply (cancel_mono ((E'.ssData k).Z ⊤).arrow).mp
      simp only [Category.assoc, hZ, Subobject.ofLE_arrow, hB,
        Subobject.ofLE_arrow_assoc])

/-- A spectral sequence packaged with a convenient infinity-page accessor. -/
structure EInftyData (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- Underlying spectral sequence. -/
  ss : SpectralSequence C ι

/-- The infinity page at grading `k`. -/
noncomputable def EInftyData.EInfty
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (eData : EInftyData C ι) (k : ι) : C :=
  (eData.ss.ssData k).eInfty

/-- A graded family of `SSData`, used as the target of the forgetful functor. -/
structure GradedSSData (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- Nested-subobject data at each grading. -/
  data : ι → SSData C

end KIP126.Core.SpectralSequence
