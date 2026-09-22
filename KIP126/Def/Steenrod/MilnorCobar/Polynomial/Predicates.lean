import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Data

/-!
# Membership in the normalized homogeneous cochains
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

/-- A polynomial is a normalized cochain of internal degree `t`. -/
def IsCochain {s : ℕ} (t : ℕ) (x : TensorPower s) : Prop :=
  x ∈ cochains s t

end

end KIP126.Steenrod.Milnor
