import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Predicates

/-!
# Polynomial preservation and membership proofs

The three mathematical properties needed to restrict the raw operations
remain open. They are not parameters of the constructed cochains.
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

/-- The coproduct differential preserves normalization and internal degree. -/
theorem differentialPolynomial_mem (s t : ℕ) (x : cochains s t) :
    IsCochain t (differentialPolynomial s x) := by
  sorry

/-- Concatenation preserves normalization and adds the two internal degrees. -/
theorem cupPolynomial_mem {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    IsCochain (t + t') (cupPolynomial x.val y.val) := by
  sorry

theorem h6Polynomial_mem : IsCochain 64 h6Polynomial := by
  sorry

end

end KIP126.Steenrod.Milnor
