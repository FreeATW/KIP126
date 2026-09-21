import KIP126.Def.Kervaire.SphereAdams

/-! Exact conditional endpoint statement for the permanent `h₆²` class. -/
namespace KIP126.Challenge.Final.H6SquarePermanent

open KIP126.Kervaire

/-- The near-126 argument proves that `h₆²` is a nonzero permanent class. -/
theorem h6_sq_permanent [D : Near126Adams] :
    ∃ hx : D.h6_square ∈
        (D.ordinaryTower (2, 128)).ZInfinity,
      (D.ordinaryTower (2, 128)).classOf D.h6_square hx ≠ 0 := by
  sorry

end KIP126.Challenge.Final.H6SquarePermanent
