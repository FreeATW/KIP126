import KIP126.Def.ClassicalAdams.H4D2.Predicates
import KIP126.External.Claims

namespace KIP126.Classical

/-- The source-backed one-line input used by this slice. Its h₄ instance is
the `j=4` specialization of the located classical one-line calculation. -/
def adamsOneLineDifferentials {stable : Adams.StableHomotopyContext}
    {A : Adams.ClassicalAdamsSS stable stable.sphere}
    (P : Adams.SphereAdamsPresentation A) : Prop :=
  Adams.h₄D₂ P

theorem adamsOneLineDifferentials_h₄ {stable : Adams.StableHomotopyContext}
    {A : Adams.ClassicalAdamsSS stable stable.sphere}
    (P : Adams.SphereAdamsPresentation A) :
    adamsOneLineDifferentials P ↔ Adams.h₄D₂ P := Iff.rfl

theorem adamsOneLineDifferentials_h₄_degrees
    {stable : Adams.StableHomotopyContext}
    {A : Adams.ClassicalAdamsSS stable stable.sphere}
    (P : Adams.SphereAdamsPresentation A)
    (proof : adamsOneLineDifferentials P) :
    ∃ statement : Adams.AdamsD₂Statement A,
      statement.source = P.h 4 ∧
        statement.target = Adams.sphereProduct P (P.h 0)
          (Adams.sphereProduct P (P.h 3) (P.h 3)) ∧
        statement.source.degree = (1, 16) ∧
        statement.target.degree = (3, 17) := by
  obtain ⟨statement, hSource, hTarget⟩ := proof
  refine ⟨statement, hSource, hTarget, ?_, ?_⟩
  · rw [hSource, P.h_degree]
    norm_num
  · rw [statement.target_degree, hSource, P.h_degree]
    norm_num [Adams.classicalAdamsTarget, Adams.classicalAdamsShift]

end KIP126.Classical

namespace KIP126.Classical.Adams

private def adamsOneLineResult {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A)
    (proof : KIP126.Classical.adamsOneLineDifferentials P) :
  KIP126.External.ExternalResult (KIP126.Classical.adamsOneLineDifferentials P) :=
  { proof := proof
    ref := (KIP126.External.externalClaimLedger.lookup
      .adamsOneLine).ref }

def cataloguedAdamsOneLine (P : SphereAdamsPresentation A)
    (proof : KIP126.Classical.adamsOneLineDifferentials P) :
    KIP126.External.CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P) :=
  { root := .adamsOneLine
    value := adamsOneLineResult P proof
    ref_eq := by rfl
    class_supported := by trivial }

/-- Consume a located one-line result.  Unlike `cataloguedAdamsOneLine`, this
direction starts from a catalogue value and extracts its supplied theorem. -/
theorem cataloguedAdamsOneLine_proof (P : SphereAdamsPresentation A)
    (input : KIP126.External.CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P)) :
    KIP126.Classical.adamsOneLineDifferentials P :=
  input.value.proof

/-- The h₄ degree calculation obtained by consuming the located external
result rather than asking the caller for an unlabelled proof. -/
theorem cataloguedAdamsOneLine_h₄_degrees (P : SphereAdamsPresentation A)
    (input : KIP126.External.CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P)) :
    ∃ statement : AdamsD₂Statement A,
      statement.source = P.h 4 ∧
        statement.target = sphereProduct P (P.h 0)
          (sphereProduct P (P.h 3) (P.h 3)) ∧
        statement.source.degree = (1, 16) ∧
        statement.target.degree = (3, 17) :=
  KIP126.Classical.adamsOneLineDifferentials_h₄_degrees P
    (cataloguedAdamsOneLine_proof P input)

structure AdamsOneLineCatalogue {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) where
  value : KIP126.External.ExternalResult
    (KIP126.Classical.adamsOneLineDifferentials P)
  ref_eq : value.ref =
    (KIP126.External.externalClaimLedger.lookup .adamsOneLine).ref

def cataloguedAdamsOneLineCanonical
    {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A)
    (proof : KIP126.Classical.adamsOneLineDifferentials P) :
    AdamsOneLineCatalogue P :=
  { value := adamsOneLineResult P proof
    ref_eq := rfl }

theorem cataloguedAdamsOneLine_h₄_degrees_bound
    {stable : StableHomotopyContext}
    {π₂ : TwoCompleteStableHomotopy stable}
    (system : SpectrumBoundClassicalAdamsSS π₂ stable.sphere)
    (P : SphereAdamsPresentation system.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P)
    (input : AdamsOneLineCatalogue P) :
    H₄D₂Bound system P algebra := by
  have canonicalInput : KIP126.External.CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P) :=
    cataloguedAdamsOneLine P input.value.proof
  exact ⟨⟨system.strongConvergence, rfl, algebra, rfl,
    KIP126.Classical.adamsOneLineDifferentials_h₄_degrees P
      (cataloguedAdamsOneLine_proof P canonicalInput)⟩⟩

end KIP126.Classical.Adams
