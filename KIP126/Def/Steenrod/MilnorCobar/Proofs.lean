import KIP126.Def.Steenrod.MilnorCobar.Predicates

/-!
# Milnor cochain multiplication and the specified cocycles

Concatenation is bilinear, and the two specified representatives are closed.
Descent of multiplication to homology still requires the general Leibniz law.
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

@[simp] theorem cup_add_left {s s' t t' : ℕ}
    (x x' : cochains s t) (y : cochains s' t') :
    cup (x + x') y = cup x y + cup x' y := by
  apply Subtype.ext
  simp [cup, cupPolynomial, add_mul]

@[simp] theorem cup_add_right {s s' t t' : ℕ}
    (x : cochains s t) (y y' : cochains s' t') :
    cup x (y + y') = cup x y + cup x y' := by
  apply Subtype.ext
  simp [cup, cupPolynomial, mul_add]

@[simp] theorem cup_smul_left {s s' t t' : ℕ}
    (a : KIP126.Core.Algebra.F2) (x : cochains s t) (y : cochains s' t') :
    cup (a • x) y = a • cup x y := by
  apply Subtype.ext
  simp [cup, cupPolynomial]

@[simp] theorem cup_smul_right {s s' t t' : ℕ}
    (a : KIP126.Core.Algebra.F2) (x : cochains s t) (y : cochains s' t') :
    cup x (a • y) = a • cup x y := by
  apply Subtype.ext
  simp [cup, cupPolynomial]

theorem h6Cochain_isCycle : IsCycle h6Cochain := by
  apply Subtype.ext
  exact h6Polynomial_differential

theorem h6SquareCochain_isCycle : IsCycle h6SquareCochain := by
  apply Subtype.ext
  exact h6SquarePolynomial_differential

end

end KIP126.Steenrod.Milnor
