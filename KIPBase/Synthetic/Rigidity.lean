/-
  KIPBase.Synthetic.Rigidity
  §3.5 Synthetic rigidity — E₂ computation of νX (§3.6),
  Adams vs λ-Bockstein (§3.8, cofiber sequence Σ^{0,r}νX →[λʳ] νX → νX/λʳ),
  E∞ comparison between synthetic and classical Adams (§3.12)
-/
import KIPBase.Mathlib
import KIPBase.Synthetic.Adams
import KIPBase.Synthetic.Nu
import KIPBase.StableHomotopy.Adams

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v u' v'

variable (𝒮 : Type u) [StableHomotopy.StableHomotopyCategory.{u, v} 𝒮]
variable (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### E∞-page of the synthetic Adams SS -/

/-- KIP Corollary A.9, Proposition 3.12: The E∞-data for the synthetic Adams
    spectral sequence of ν(X). -/
axiom SynAdamsEInfty (𝒮 : Type u) [StableHomotopy.StableHomotopyCategory.{u, v} 𝒮]
    (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]
    (X : 𝒮) : EInftyData AddCommGrpCat.{0} (ℤ × ℤ × ℤ)

/-- Formalization bridge: The E∞-data is associated with the synthetic Adams
    SS for ν(X). Links `SynAdamsEInfty` to `SynAdamsSS`. -/
axiom synAdamsEInfty_ss (X : 𝒮) :
    (SynAdamsEInfty 𝒮 Syn X).ss = SynAdamsSS Syn ((nu 𝒮 Syn).obj X)

/-! ### Rigidity theorem

The rigidity theorem (KIP Theorem A.8) states:
  E₂^{s,t,w}(SynAdamsSS(νX)) ≅ E₂^{s,t}(AdamsSS(X)) ⊗ F₂[λ]_w
with differential correspondence d_r^syn(x) = λ^{r-1} · d_r^cl(x).

Since the full statement requires Z[λ]-module infrastructure not yet
formalized, we axiomatize the key consequences: degeneration transfer
and weight-range vanishing. -/

/-- KIP Theorem A.8 (rigidity — degeneration transfer): If the classical
    Adams SS degenerates at page N, then the synthetic Adams SS for ν(X)
    also degenerates at page N. -/
axiom rigidity_degeneration (X : 𝒮) (N : ℤ) :
    (StableHomotopy.AdamsSS 𝒮 X).DegeneratesAt N →
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).DegeneratesAt N

/-- KIP Theorem A.8 (rigidity — negative weight vanishing): For w < 0,
    E₂^{s,t,w}(SynAdamsSS(νX)) = 0. This is because E₂ ≅ E₂^cl ⊗ F₂[λ]
    and F₂[λ] has no negative degree part. -/
axiom rigidity_neg_weight_vanishing (X : 𝒮) (s t w : ℤ) (hw : w < 0) :
    IsZero ((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page 2 (s, t, w))

/-- KIP Theorem A.8 (rigidity — above-diagonal vanishing): For w > t,
    E_r^{s,t,w}(SynAdamsSS(νX)) = 0 for all r ≥ 2. This reflects the
    F₂[λ]-module structure: the polynomial degree w is bounded by t. -/
axiom rigidity_above_diag_vanishing (X : 𝒮) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (htw : t < w) :
    IsZero ((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w))

/-! ### λ-Bockstein spectral sequence

The λ-Bockstein SS is obtained from the exact couple
  Σ^{0,1}(νX) →[λ] νX → νX/λ.
The rigidity theorem implies it coincides with the synthetic Adams SS. -/

/-- KIP Theorem A.1 (λ-Bockstein identification): The synthetic Adams SS
    for νX coincides with the λ-Bockstein SS. The key consequence: both
    start at page r₀ = 2 and have the same differential degrees. Full
    E₂-level identification requires Z[λ]-module formalization. -/
axiom lambda_bockstein_iso (X : 𝒮) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).r₀ = 2

/-! ### E∞ computations -/

/-- E∞ vanishing for ν(X) (KIP Prop 3.12):
    For t < w, E∞^{s,t,w}(νX) = 0.
    The permanent cycles in weight w cannot contribute below the
    diagonal t = w. -/
theorem einfty_nuX (X : 𝒮) (s t w : ℤ) (htw : t < w) :
    IsZero ((SynAdamsEInfty 𝒮 Syn X).EInfty (s, t, w)) := by
  -- Strategy: use rigidity_above_diag_vanishing to show all pages vanish,
  -- then propagate to E∞ via EInftyData.eInfty_isZero_of_page_isZero.
  apply EInftyData.eInfty_isZero_of_page_isZero
  intro r hr
  -- Rewrite the SS to use SynAdamsSS via synAdamsEInfty_ss
  rw [synAdamsEInfty_ss 𝒮 Syn X]
  -- The starting page is r₀ = 2 (from synAdamsSS_r0)
  -- We need 2 ≤ r, which follows from r₀ = 2 and hr : r₀ ≤ r
  have hr₀ : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).r₀ = 2 :=
    synAdamsSS_r0 Syn ((nu 𝒮 Syn).obj X)
  have h2r : 2 ≤ r := by
    have := synAdamsEInfty_ss (𝒮 := 𝒮) (Syn := Syn) X
    rw [this] at hr
    rw [hr₀] at hr
    exact hr
  exact rigidity_above_diag_vanishing 𝒮 Syn X r h2r s t w htw

/-- KIP Corollary A.9, Proposition 3.12: E∞ weight monotonicity for ν(X).
    For w₁ ≤ w₂ ≤ t, there is a natural surjection
    E∞^{s,t,w₁}(νX) ↠ E∞^{s,t,w₂}(νX).
    This reflects the quotient map Z∞/B_{1+t-w₁} → Z∞/B_{1+t-w₂}
    arising from B_{1+t-w₁} ⊆ B_{1+t-w₂}. -/
axiom einfty_nuX_weight_map (X : 𝒮) (s t w₁ w₂ : ℤ)
    (hw : w₁ ≤ w₂) (hw₂ : w₂ ≤ t) :
    (SynAdamsEInfty 𝒮 Syn X).EInfty (s, t, w₁) ⟶
      (SynAdamsEInfty 𝒮 Syn X).EInfty (s, t, w₂)

/-- KIP Corollary A.9, Proposition 3.12: The weight maps are
    epimorphisms (surjections). -/
axiom einfty_nuX_weight_map_epi (X : 𝒮) (s t w₁ w₂ : ℤ)
    (hw : w₁ ≤ w₂) (hw₂ : w₂ ≤ t) :
    Epi (einfty_nuX_weight_map 𝒮 Syn X s t w₁ w₂ hw hw₂)

/-- KIP Corollary A.11, Proposition 3.13: E∞ of ν(X)/λʳ vanishing.
    E∞^{s,t,w}(νX/λʳ) = 0 outside the range 0 ≤ t - w < r.
    The nonzero entries are isomorphic to Z_{r-t+w}/B_{1+t-w}
    of the classical Adams SS. -/
axiom einfty_nuX_mod_lambda (X : 𝒮) (r : ℕ) (hr : 0 < r)
    (s t w : ℤ) (h : t - w < 0 ∨ (r : ℤ) ≤ t - w) :
    IsZero ((SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) r)).Page 2
      (s, t, w))

end KIPBase.Synthetic
