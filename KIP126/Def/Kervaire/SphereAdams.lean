import KIP126.Def.ClassicalAdams.Permanence.Data
import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.Def.Kervaire.Theta5.Data

/-!
# Semantic interface for the near-126 Adams endpoint

The page class used below is the existing `ClassicalAdamsSS` object.  The
presentation supplies its named sphere classes and multiplication, so `h₆²`
is derived by `KIP126.Classical.Adams.h6Square` rather than introduced as a
second, unrelated carrier element.
-/

namespace KIP126.Kervaire

/-- Semantic near-126 data used by the open differential statements.

The fields are predicates and candidate data; none of them asserts the final
permanence conclusion. -/
class Near126Adams where
  stable : KIP126.Classical.Adams.StableHomotopyContext
  adams : KIP126.Classical.Adams.ClassicalAdamsSS stable stable.sphere
  presentation : KIP126.Classical.Adams.SphereAdamsPresentation adams
  lawfulAlgebra : KIP126.Classical.Adams.SphereAdamsAlgebraPresentation presentation
  Carrier : Type
  [carrierAddCommGroup : AddCommGroup Carrier]
  d12_value : Carrier
  d12_target : Carrier
  differential : ℕ → Prop
  c3 : Prop
  c4 : Prop
  c5 : Prop

attribute [instance] Near126Adams.carrierAddCommGroup

namespace Near126Adams

variable (D : Near126Adams)

/-- The named page-2 class represented by `h₆²` for the selected Adams object. -/
def h6_square : KIP126.Classical.Adams.AdamsClass D.adams :=
  KIP126.Classical.Adams.h6Square D.presentation

/-- The final spectral-sequence endpoint proposition for the selected sphere
Adams sequence. -/
def h6_square_isPermanent : Prop :=
  D.h6_square.IsPermanent

/-- The displayed `d₁₂` candidate is nonzero. -/
def d12_differential_is_nonzero : Prop :=
  D.d12_value = D.d12_target ∧ D.d12_value ≠ 0

end Near126Adams

/-- Semantic choice data for the existential/universal `C₄` and `C₅`
equivalences. -/
class ChoiceConditions where
  Carrier : Type
  [carrierAddCommGroup : AddCommGroup Carrier]
  context : Theta5ChoiceContext (Carrier := Carrier)
  c4_at : Carrier → Prop
  c5_at : Carrier → Prop

attribute [instance] ChoiceConditions.carrierAddCommGroup

end KIP126.Kervaire
