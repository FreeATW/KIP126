import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Normalization.Proofs
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Two

/-!
# Polynomial preservation and membership proofs

Concatenation preserves normalization and degree, and the specified
representatives are normalized cocycles. Preservation by the general
coproduct differential is the remaining open obligation in this module.
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Core.Algebra MvPolynomial

/-- The coproduct differential preserves normalization and internal degree. -/
theorem differentialPolynomial_mem (s t : ℕ) (x : cochains s t) :
    IsCochain t (differentialPolynomial s x) := by
  constructor
  · change IsWeightedHomogeneous weight (differentialPolynomial s x.val) t
    simp only [differentialPolynomial, LinearMap.add_apply, LinearMap.sum_apply,
      AlgHom.toLinearMap_apply]
    exact ((homogeneous_rename_slots Fin.succ x.property.1).add
      (homogeneous_rename_slots Fin.castSucc x.property.1)).add
      (IsWeightedHomogeneous.sum Finset.univ (fun slot => splitSlot slot x.val) t
        (fun slot _ => homogeneous_splitSlot slot x.property.1))
  · change differentialPolynomial s x.val ∈
      (⨅ slot : Fin (s + 1), LinearMap.ker (augmentSlot slot).toLinearMap)
    rw [Submodule.mem_iInf]
    intro slot
    exact differentialPolynomial_normalized x.val
      (fun i => (Submodule.mem_iInf _).mp x.property.2 i) slot

/-- Concatenation preserves normalization and adds the two internal degrees. -/
theorem cupPolynomial_mem {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    IsCochain (t + t') (cupPolynomial x.val y.val) := by
  constructor
  · exact (homogeneous_rename_slots (Fin.castAdd s') x.property.1).mul
      (homogeneous_rename_slots (Fin.natAdd s) y.property.1)
  · change cupPolynomial x.val y.val ∈
      (⨅ slot : Fin (s + s'), LinearMap.ker (augmentSlot slot).toLinearMap)
    rw [Submodule.mem_iInf]
    intro slot
    refine Fin.addCases (fun i => ?_) (fun i => ?_) slot
    · change augmentSlot (i.castAdd s') (cupPolynomial x.val y.val) = 0
      have hx : augmentSlot i x.val = 0 := (Submodule.mem_iInf _).mp x.property.2 i
      rw [cupPolynomial, map_mul,
        augmentSlot_rename (Fin.castAdd s') (Fin.castAdd_injective s s'), hx, map_zero, zero_mul]
    · change augmentSlot (i.natAdd s) (cupPolynomial x.val y.val) = 0
      have hy : augmentSlot i y.val = 0 := (Submodule.mem_iInf _).mp y.property.2 i
      rw [cupPolynomial, map_mul,
        augmentSlot_rename (Fin.natAdd s) (Fin.natAdd_injective s' s), hy, map_zero, mul_zero]

theorem h6Polynomial_mem : IsCochain 64 h6Polynomial := by
  constructor
  · simpa [h6Polynomial, weight] using
      (MvPolynomial.isWeightedHomogeneous_X (R := KIP126.Core.Algebra.F2)
        (@weight 1) (0, 0)).pow 64
  · change h6Polynomial ∈ (⨅ slot : Fin 1, LinearMap.ker (augmentSlot slot).toLinearMap)
    rw [Submodule.mem_iInf]
    intro slot
    have hslot : slot = 0 := Subsingleton.elim _ _
    subst slot
    simp [LinearMap.mem_ker, augmentSlot, h6Polynomial]

/-- The primitive power representative is closed, independently of the
restriction of the differential to normalized cochains. -/
theorem h6Polynomial_differential : differentialPolynomial 1 h6Polynomial = 0 := by
  have hp (x y : TensorPower 2) : (x + y) ^ 64 = x ^ 64 + y ^ 64 :=
    add_pow_char_pow x y 2 6
  simp [differentialPolynomial, h6Polynomial, insertLeft, insertRight,
    splitSlot, coproductGenerator, xi, Finset.sum_range_succ, hp,
    add_assoc, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left]

/-- The concatenated square is closed at the polynomial level. -/
theorem h6SquarePolynomial_differential :
    differentialPolynomial 2 (cupPolynomial h6Polynomial h6Polynomial) = 0 := by
  have hp (x y : TensorPower 3) : (x + y) ^ 64 = x ^ 64 + y ^ 64 :=
    add_pow_char_pow x y 2 6
  simp [differentialPolynomial, cupPolynomial, h6Polynomial, insertLeft, insertRight,
    splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ, hp]
  ring_nf
  simp [CharTwo.two_eq_zero]

end

end KIP126.Steenrod.Milnor
