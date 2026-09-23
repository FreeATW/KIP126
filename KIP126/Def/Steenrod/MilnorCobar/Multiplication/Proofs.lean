import KIP126.Def.Steenrod.MilnorCobar.Reindex.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Proofs

/-! # The cobar Leibniz formula -/

namespace KIP126.Steenrod.Milnor

noncomputable section

/-- Concatenation satisfies the Leibniz identity over `𝔽₂`. -/
theorem differential_cup {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    differential (s + s') (t + t') (cup x y) =
      reindex (by omega) rfl (cup (differential s t x) y) +
      reindex (by omega) rfl (cup x (differential s' t' y)) := by
  apply Subtype.ext
  change differentialPolynomial (s + s') (cupPolynomial x.val y.val) =
    (reindex _ _ (cup (differential s t x) y)).val +
    (reindex _ _ (cup x (differential s' t' y))).val
  rw [reindex_cup_val, reindex_cup_val]
  exact differentialPolynomial_cup_blocks x.val y.val

@[simp] theorem cup_zero_left {s s' t t' : ℕ} (y : cochains s' t') :
    cup (0 : cochains s t) y = 0 := by
  apply Subtype.ext
  simp [cup, cupPolynomial]

@[simp] theorem cup_zero_right {s s' t t' : ℕ} (x : cochains s t) :
    cup x (0 : cochains s' t') = 0 := by
  apply Subtype.ext
  simp [cup, cupPolynomial]

/-- Products of cocycles are cocycles. -/
theorem cup_isCycle {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t')
    (hx : IsCycle x) (hy : IsCycle y) : IsCycle (cup x y) := by
  change differential _ _ (cup x y) = 0
  rw [differential_cup, hx, hy, cup_zero_left, cup_zero_right, map_zero, map_zero, zero_add]

end

end KIP126.Steenrod.Milnor
