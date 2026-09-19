import KIP126.Def.Kervaire.Theta5.Predicates
import KIP126.Def.Kervaire.Setup.Data
import KIP126.External.Literature.Kervaire

/-! Exact conditional dimension-126 existence statement. -/
namespace KIP126.Challenge.Geometry.Thm1_1Dimension126

open KIP126.Kervaire
open KIP126.Classical.Adams
open KIP126.External

abbrev ManifoldOf {C : StableHomotopyContext} {H : StableHomotopyData C}
    (F : FramedKervaireContext H) := Sigma F.Manifold

def dimension {C : StableHomotopyContext} {H : StableHomotopyData C}
    (F : FramedKervaireContext H) : ManifoldOf F → ℕ := fun M => M.1

def kervaireOne {C : StableHomotopyContext} {H : StableHomotopyData C}
    (F : FramedKervaireContext H) : ManifoldOf F → Prop :=
  fun M => F.hasKervaireInvariantOne M.2

structure Input where
  C : StableHomotopyContext
  H : StableHomotopyData C
  framed : FramedKervaireContext H
  permanent : ℕ → Prop
  browder : CataloguedExternalResult
    (BrowderCriterionStatement (dimension framed) (kervaireOne framed) permanent)
  h6Permanent : permanent 6

/-- If the selected sphere input has the permanent `h₆²` class, a framed
Kervaire-invariant-one manifold exists in dimension 126. -/
def statement (I : Input) : Prop :=
  ∃ M : I.framed.Manifold 126,
    I.framed.closedSmoothFramed M ∧
      I.framed.hasKervaireInvariantOne M

end KIP126.Challenge.Geometry.Thm1_1Dimension126
