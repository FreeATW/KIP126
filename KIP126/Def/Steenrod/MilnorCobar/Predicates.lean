import KIP126.Def.Steenrod.MilnorCobar.Data

/-!
# Normalized Milnor cocycle predicate
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

/-- A normalized cochain is a cocycle when its cobar differential is zero. -/
def IsCycle {s t : ℕ} (x : cochains s t) : Prop :=
  differential s t x = 0

end

end KIP126.Steenrod.Milnor
