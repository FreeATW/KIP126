import KIP126.Challenge.Geometry.Thm1_1Dimension126.Statement

/-! Exact open statement for the final Kervaire dimension list. -/
namespace KIP126.Challenge.Geometry.Cor1_2Dimensions

open KIP126.Challenge.Geometry.Thm1_1Dimension126
open KIP126.Classical.Adams
open KIP126.External
open KIP126.Kervaire

structure Input where
  base : Thm1_1Dimension126.Input
  hhr : CataloguedExternalResult
    (HHRNonexistenceStatement (dimension base.framed) (kervaireOne base.framed))

/-- The exact dimensions carrying framed Kervaire invariant one are
`2, 6, 14, 30, 62, 126`. -/
def statement (I : Input) : Prop :=
  ∀ n : ℕ,
    ((∃ M : ManifoldOf I.base.framed,
        dimension I.base.framed M = n ∧ kervaireOne I.base.framed M) ↔
      n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126)

end KIP126.Challenge.Geometry.Cor1_2Dimensions
