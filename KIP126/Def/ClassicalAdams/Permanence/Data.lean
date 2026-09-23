import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.Def.SpectralSequence.Permanence.Data

/-! Permanence predicates for actual classes in a classical Adams sequence. -/

namespace KIP126.Classical.Adams

open KIP126.Core.SpectralSequence

/-- A named `E₂` Adams class is permanent when its actual page representative
has compatible nonzero descendants on every later page. -/
def AdamsClass.IsPermanent
    {stable : StableHomotopyContext} {X : stable.Spectrum}
    {A : ClassicalAdamsSS stable X} (x : AdamsClass A) : Prop :=
  KIP126.Core.SpectralSequence.IsPermanent
    A.sequence 2 (by norm_num) x.degree x.representative

/-- The statement that the chosen sphere class `h₆²` is permanent. -/
def H6SquareIsPermanent
    {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) : Prop :=
  (h6Square P).IsPermanent

theorem AdamsClass.IsPermanent.ne_zero
    {stable : StableHomotopyContext} {X : stable.Spectrum}
    {A : ClassicalAdamsSS stable X} {x : AdamsClass A}
    (h : x.IsPermanent) : x.representative ≠ 0 := by
  exact KIP126.Core.SpectralSequence.IsPermanent.ne_zero h

end KIP126.Classical.Adams
