import KIP126.Def.ClassicalAdams.Permanence.Data

/-! The sphere `h₆²` permanence statement uses its actual `E₂` representative. -/

namespace KIP126.Checks.ClassicalAdams.Permanence

open KIP126.Classical.Adams

variable {stable : StableHomotopyContext}
variable {A : ClassicalAdamsSS stable stable.sphere}

example (P : SphereAdamsPresentation A) :
    H6SquareIsPermanent P ↔ (h6Square P).IsPermanent := by
  rfl

example (P : SphereAdamsPresentation A) (h : H6SquareIsPermanent P) :
    (h6Square P).representative ≠ 0 := h.ne_zero

end KIP126.Checks.ClassicalAdams.Permanence
