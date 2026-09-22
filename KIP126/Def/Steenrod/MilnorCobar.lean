import KIP126.Def.Algebra.Coefficients.Data
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# The normalized mod-two Milnor cobar construction

The dual Steenrod algebra is the polynomial algebra on `ξ₁, ξ₂, ...`,
with `|ξᵢ| = 2ⁱ - 1` and
`Δ ξₙ = ∑ i = 0,...,n, ξₙ₋ᵢ^(2ⁱ) ⊗ ξᵢ`, where `ξ₀ = 1`.
Tensor powers are polynomial algebras with an additional slot index.
Normalization means that augmentation in any slot is zero.

The standard `h₆` cocycle is `[ξ₁^64]`; its square is the concatenation
`[ξ₁^64 | ξ₁^64]`.  No named Ext class or product is supplied as input.
The degree, normalization, and cocycle proofs remain explicit obligations.

Reference for the standard representative: W. M. Singer, *Rings of symmetric
functions as modules over the Steenrod algebra*, Algebr. Geom. Topol. 8
(2008), p. 548, immediately after (2–13).
https://msp.org/agt/2008/8-1/agt-v8-n1-p17-p.pdf

The coproduct convention is Boardman, *Stable operations in generalized
cohomology*, p. 208, equation (7.4):
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/boardman-8.pdf
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Core.Algebra MvPolynomial
open scoped BigOperators

/-- The `s`fold tensor power of the polynomial dual Steenrod algebra.
The generator `(slot,j)` denotes `ξ_(j+1)` in that slot. -/
abbrev TensorPower (s : ℕ) := MvPolynomial (Fin s × ℕ) F2

/-- Milnor's grading, independent of the tensor slot. -/
def weight {s : ℕ} (a : Fin s × ℕ) : ℕ := 2 ^ (a.2 + 1) - 1

/-- Include the convention `ξ₀ = 1` in the polynomial formula. -/
def xi {s : ℕ} (slot : Fin s) : ℕ → TensorPower s
  | 0 => 1
  | j + 1 => MvPolynomial.X (slot, j)

/-- The Milnor coproduct, inserted at the specified adjacent tensor slots. -/
def coproductGenerator {s : ℕ} (slot : Fin s) (j : ℕ) : TensorPower (s + 1) :=
  ∑ i ∈ Finset.range (j + 2),
    xi slot.castSucc (j + 1 - i) ^ (2 ^ i) * xi slot.succ i

/-- Apply the coproduct in one tensor slot. -/
def splitSlot {s : ℕ} (slot : Fin s) : TensorPower s →ₐ[F2] TensorPower (s + 1) :=
  MvPolynomial.aeval fun a =>
    if a.1 = slot then coproductGenerator slot a.2
    else MvPolynomial.X (if a.1 < slot then a.1.castSucc else a.1.succ, a.2)

/-- Insert the coaugmentation at the left end. -/
def insertLeft (s : ℕ) : TensorPower s →ₐ[F2] TensorPower (s + 1) :=
  MvPolynomial.rename fun a => (a.1.succ, a.2)

/-- Insert the coaugmentation at the right end. -/
def insertRight (s : ℕ) : TensorPower s →ₐ[F2] TensorPower (s + 1) :=
  MvPolynomial.rename fun a => (a.1.castSucc, a.2)

/-- Augment one slot by sending all its positive-degree generators to zero. -/
def augmentSlot {s : ℕ} (slot : Fin s) : TensorPower s →ₐ[F2] TensorPower s :=
  MvPolynomial.aeval fun a => if a.1 = slot then 0 else MvPolynomial.X a

/-- Homogeneous normalized cobar cochains. -/
def cochains (s t : ℕ) : Submodule F2 (TensorPower s) :=
  MvPolynomial.weightedHomogeneousSubmodule F2 weight t ⊓
    ⨅ slot : Fin s, LinearMap.ker (augmentSlot slot).toLinearMap

/-- The characteristic-two cobar differential before restriction to normalized cochains. -/
def differentialPolynomial (s : ℕ) : TensorPower s →ₗ[F2] TensorPower (s + 1) :=
  (insertLeft s).toLinearMap + (insertRight s).toLinearMap +
    ∑ slot : Fin s, (splitSlot slot).toLinearMap

/-- The coproduct differential preserves normalization and internal degree. -/
theorem differentialPolynomial_mem (s t : ℕ) (x : cochains s t) :
    differentialPolynomial s x ∈ cochains (s + 1) t := by
  sorry

/-- The actual normalized cobar differential. -/
def differential (s t : ℕ) : cochains s t →ₗ[F2] cochains (s + 1) t :=
  ((differentialPolynomial s).comp (cochains s t).subtype).codRestrict _
    (differentialPolynomial_mem s t)

/-- Concatenation of tensor words, expressed by disjoint variable renamings. -/
def cupPolynomial {s s' : ℕ} (x : TensorPower s) (y : TensorPower s') :
    TensorPower (s + s') :=
  MvPolynomial.rename (fun a : Fin s × ℕ => (a.1.castAdd s', a.2)) x *
    MvPolynomial.rename (fun a : Fin s' × ℕ => (a.1.natAdd s, a.2)) y

/-- Concatenation preserves normalization and adds the two internal degrees. -/
theorem cupPolynomial_mem {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    cupPolynomial x.val y.val ∈ cochains (s + s') (t + t') := by
  sorry

/-- The cochain product used to define the square. -/
def cup {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    cochains (s + s') (t + t') :=
  ⟨cupPolynomial x.val y.val, cupPolynomial_mem x y⟩

/-- The polynomial representative `[ξ₁^64]`. -/
def h6Polynomial : TensorPower 1 := MvPolynomial.X (0, 0) ^ 64

theorem h6Polynomial_mem : h6Polynomial ∈ cochains 1 64 := by
  sorry

/-- The standard normalized cocycle representing `h₆`. -/
def h6Cochain : cochains 1 64 := ⟨h6Polynomial, h6Polynomial_mem⟩

/-- The square is the actual cochain concatenation product. -/
def h6SquareCochain : cochains 2 128 := cup h6Cochain h6Cochain

theorem h6Cochain_isCycle : differential 1 64 h6Cochain = 0 := by
  sorry

theorem h6SquareCochain_isCycle : differential 2 128 h6SquareCochain = 0 := by
  sorry

end

end KIP126.Steenrod.Milnor
