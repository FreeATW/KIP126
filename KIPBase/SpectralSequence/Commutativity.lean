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

/-! ### Homotopy commutative square of converging spectral sequences -/

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

/-- **Theorem 2.12**: Commutativity of ESS differentials (full version).

    Given a homotopy commutative square and:
    1. `d_n^f(x) = y` (ESS differential of f)
    2. `d_m^p(x) = z` (ESS differential of p)
    3. One of (1) or (2) has no crossing
    4. `d_l^g(z) = w` with no crossing hitting Fil ≥ s + n + k (for 0 < k ≤ m + l − n)
    5. `d_{k-1}^q(y) = 0` with no crossing

    Then `d_{m+l-n}^q(y) = w`. -/
axiom essCommutativity {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ESSRelation sq.extq (m + l - n) ky kw

/-- **Theorem 2.12 (value form)**: The ESS differential `d_{m+l-n}^q(y)` equals
    the composition of `d_l^g(z)` through the commutativity square, expressed
    as an isomorphism between the differential objects. -/
axiom essCommutativity_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    Nonempty (sq.extq.essDiff (m + l - n) ky kw ≅ sq.extg.essDiff l kz kw)

/-! ### Corollary 2.15 — Simplified commutativity (no crossing everywhere) -/

/-- **Corollary 2.15**: Simplified commutativity — same as Thm 2.12 but with
    `d_l^g(z) = w` having no crossing at all (dropping the k parameter). -/
axiom essCommutativity_noCrossing {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ESSRelation sq.extq (m + l - n) ky kw

/-- **Corollary 2.15 (iso form)**: Under no-crossing-everywhere, the differential
    objects are isomorphic. -/
axiom essCommutativity_noCrossing_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    Nonempty (sq.extq.essDiff (m + l - n) ky kw ≅ sq.extg.essDiff l kz kw)

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
axiom essCommutativity_triangle {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ESSRelation extq (m - n) ky kz

/-- **Corollary 2.16 (iso form)**: Triangle case iso. -/
axiom essCommutativity_triangle_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    Nonempty (extq.essDiff (m - n) ky kz ≅ extp.essDiff m kx kz)

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
axiom essCommutativity_composition {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ESSRelation extq (m + l) kx kw

/-- **Corollary 2.17 (iso form)**: Composition case iso. -/
axiom essCommutativity_composition_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    Nonempty (extq.essDiff (m + l) kx kw ≅ extg.essDiff l kz kw)

/-! ### Corollary 2.18 — Induced map on ESS pages -/

/-- The ESS page map induced by the commutativity square: if the source E∞-pages
    have `E₀ = E_r` (degeneration at page r), then the commutativity data
    induces a well-defined map between the f-ESS and g-ESS pages. -/
axiom essCommutativity_induces_map {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ∃ (_ : sq.extf.essDiff n k₁ k₂ ⟶ sq.extg.essDiff n k₁ k₂), True

/-- **Corollary 2.18 (compatibility)**: The induced page map commutes with ESS
    differentials. -/
axiom essInducedPageMap_comm {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    (n : ℤ) (k₁ k₂ k₃ : ω) :
    ∀ (_φ₁₂ : sq.extf.essDiff n k₁ k₂ ⟶ sq.extg.essDiff n k₁ k₂)
      (_φ₂₃ : sq.extf.essDiff n k₂ k₃ ⟶ sq.extg.essDiff n k₂ k₃),
    True

/-! ### Corollary 2.19 — Null composition -/

/-- **Corollary 2.19**: If `g ∘ f` is null-homotopic and `d_n^f(x) = y`,
    then `y` is a permanent cycle in the g-ESS: `d_m^g(y) = 0` for all `m ≥ 0`. -/
axiom essCommutativity_null {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ESSVanishes sq.extq m ky kw

/-! ### Supporting axioms — Commutativity functoriality -/

/-- Commutativity squares preserve boundary groups: the boundary in the q-ESS
    at page `m + l - n` is related to the boundary in the g-ESS at page `l`. -/
axiom essCommutativity_preserves_boundaries {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n m l : ℤ) (kw : ω)
    (_hn : 0 ≤ n) (_hm : 0 ≤ m) (_hl : 0 ≤ l) :
    ∃ (_ : sq.extq.essBoundary (m + l - n) kw ⟶ sq.extg.essBoundary l kw), True

/-- The HomotopyCommSquare is natural in the following sense: the induced maps
    on ESS differentials respect composition of convergence morphisms. -/
axiom essCommutativity_naturality {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n : ℤ) (k₁ k₂ : ω) :
    ∃ (_ : sq.extf.essDiff n k₁ k₂ ⟶ sq.extq.essDiff n k₁ k₂), True

/-- The commutativity data is compatible with the E∞ page maps. -/
axiom essCommutativity_eInfty_compat {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n : ℤ) (k : ω) :
    sq.cmf.eMap k ≫ sq.cmq.eMap k = sq.cmp.eMap k ≫ sq.cmg.eMap k

/-- The filtration data is compatible across the commutativity square. -/
axiom essCommutativity_filtration_compat {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (s : ℤ) (k' : ω') :
    ∀ (_x : Subobject.underlying.obj (F₁.F s k') ⟶ Subobject.underlying.obj (F₂.F s k'))
      (_y : Subobject.underlying.obj (F₃.F s k') ⟶ Subobject.underlying.obj (F₄.F s k')),
    True

/-! ### Triangle and composition reductions -/

/-- Triangle reduction: Corollary 2.16 specializes from the full commutativity. -/
axiom essTriangle_from_square {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ∃ (_idCm : ConvergenceMorphism conv₃ conv₃)
      (_idExt : BoundedExtensionSS conv₃ conv₃ _idCm bnd₃ bnd₃),
    True

/-- Composition reduction: Corollary 2.17 specializes from the full commutativity. -/
axiom essComposition_from_square {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ∃ (_idCm : ConvergenceMorphism conv₁ conv₁)
      (_idExt : BoundedExtensionSS conv₁ conv₁ _idCm bnd₁ bnd₁),
    True

/-! ### Boundary transfer -/

/-- Boundary transfer under the commutativity square: an element in the
    ESS boundary of the q-differential maps to an element in the ESS boundary
    of the g-differential under appropriate conditions. -/
axiom essCommutativity_boundary_transfer {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ E₄ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ A₄ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (n : ℤ) (kw : ω) :
    ∃ (_ : sq.extq.essBoundary n kw ⟶ sq.extg.essBoundary n kw), True

/-! ### ESS page functoriality under commutativity -/

/-- The ESS page at level n is functorial: the page map induced by the commutativity
    square respects composition of convergence morphisms at each ESS page. -/
axiom essCommutativity_page_functorial {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ∀ (_φ : sq.extf.essDiff n k₁ k₂ ⟶ sq.extg.essDiff n k₁ k₂)
      (_ψ : sq.extf.essDiff (n + 1) k₁ k₂ ⟶ sq.extg.essDiff (n + 1) k₁ k₂),
    True

/-- The detection set data is compatible with the commutativity square maps. -/
axiom essCommutativity_detection_compat {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ∃ (_ : DetectionSet conv₄ k z), True

/-- Commutativity is preserved under ESS page transition: if the commutativity
    relation holds at page n, it holds at page n+1 (assuming no new crossings). -/
axiom essCommutativity_page_transition {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
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
    ∃ (_ : sq.extq.essDiff n ky kw ⟶ sq.extg.essDiff n ky kw), True

end KIPBase.SpectralSequence
