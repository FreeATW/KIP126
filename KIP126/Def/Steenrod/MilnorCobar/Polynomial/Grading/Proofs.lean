import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Predicates

/-!
# Internal grading of the Milnor coproduct
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Core.Algebra MvPolynomial

/-- Renaming tensor slots does not change internal degree. -/
theorem homogeneous_rename_slots {s s' t : ℕ} (f : Fin s → Fin s')
    {x : TensorPower s} (hx : IsWeightedHomogeneous weight x t) :
    IsWeightedHomogeneous weight (rename (fun a : Fin s × ℕ => (f a.1, a.2)) x) t := by
  induction hx using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero F2 (@weight s') t
  | add x y hx hy ihx ihy => simpa using ihx.add ihy
  | monomial d r hd =>
    rw [rename_monomial]
    apply isWeightedHomogeneous_monomial
    rw [← hd]
    simp only [Finsupp.weight_apply, weight, smul_eq_mul]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]

/-- Substitution of homogeneous polynomials of the prescribed generator
weights preserves the weighted degree. -/
theorem homogeneous_aeval {σ τ : Type*} {R : Type*} [CommSemiring R]
    (w : σ → ℕ) (w' : τ → ℕ) (f : σ → MvPolynomial τ R)
    (hf : ∀ a, IsWeightedHomogeneous w' (f a) (w a))
    {x : MvPolynomial σ R} {t : ℕ} (hx : IsWeightedHomogeneous w x t) :
    IsWeightedHomogeneous w' (aeval f x) t := by
  classical
  induction hx using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R w' t
  | add x y hx hy ihx ihy => simpa using ihx.add ihy
  | monomial d r hd =>
    rw [aeval_monomial]
    have h := (IsWeightedHomogeneous.prod d.support
      (fun a => f a ^ d a) (fun a => d a * w a)
      (fun a _ => by simpa [nsmul_eq_mul] using (hf a).pow (d a))).C_mul r
    have hd' : ∑ a ∈ d.support, d a * w a = t := by
      simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using hd
    simpa only [Finsupp.prod, hd', MvPolynomial.algebraMap_eq] using h

/-- The convention `ξ₀ = 1` respects Milnor's grading. -/
theorem homogeneous_xi {s : ℕ} (slot : Fin s) (j : ℕ) :
    IsWeightedHomogeneous weight (xi slot j) (2 ^ j - 1) := by
  cases j with
  | zero => simpa [xi] using isWeightedHomogeneous_one F2 (@weight s)
  | succ j => exact isWeightedHomogeneous_X (R := F2) weight (slot, j)

/-- Each summand of Milnor's coproduct has the original generator's degree. -/
theorem homogeneous_coproductGenerator {s : ℕ} (slot : Fin s) (j : ℕ) :
    IsWeightedHomogeneous weight (coproductGenerator slot j) (2 ^ (j + 1) - 1) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  have hi' : i ≤ j + 1 := by
    have := Finset.mem_range.mp hi
    omega
  have he : (2 ^ i) * (2 ^ (j + 1 - i) - 1) + (2 ^ i - 1) = 2 ^ (j + 1) - 1 := by
    have hp : 2 ^ (j + 1 - i) * 2 ^ i = 2 ^ (j + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hi']
    have h₁ : 1 ≤ 2 ^ (j + 1 - i) := Nat.one_le_pow _ _ (by omega)
    have h₂ : 1 ≤ 2 ^ i := Nat.one_le_pow _ _ (by omega)
    have h₃ : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
    nlinarith [Nat.sub_add_cancel h₁, Nat.sub_add_cancel h₂, Nat.sub_add_cancel h₃]
  simpa only [nsmul_eq_mul, Nat.cast_id, he] using
    ((homogeneous_xi slot.castSucc (j + 1 - i)).pow (2 ^ i)).mul
      (homogeneous_xi slot.succ i)

/-- Splitting a tensor slot by the coproduct preserves internal degree. -/
theorem homogeneous_splitSlot {s t : ℕ} (slot : Fin s) {x : TensorPower s}
    (hx : IsWeightedHomogeneous weight x t) :
    IsWeightedHomogeneous weight (splitSlot slot x) t := by
  apply homogeneous_aeval weight weight _ _ hx
  intro a
  by_cases h : a.1 = slot
  · simpa only [if_pos h, weight] using homogeneous_coproductGenerator slot a.2
  · simp only [if_neg h]
    exact isWeightedHomogeneous_X (R := F2) weight _

end

end KIP126.Steenrod.Milnor
