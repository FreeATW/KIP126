import KIP126.Def.ClassicalESS.Eta.Predicates

namespace KIP126.Classical.ExtensionSS

open CategoryTheory CategoryTheory.Limits
open KIP126.Classical.Adams
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence
open KIP126.External

@[simp] theorem etaESSShape_rel (n : ℤ) (b : Index) :
    (etaESSShape n).Rel b (b + (n, n)) := by
  simp [etaESSShape]

theorem abutment_component {stable : StableHomotopyContext} {X Y : stable.Spectrum}
  {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
  (D : EtaESSInput source target) (b : Index) :
    abutment D b = biprod (kernel (D.adapter.etaMap b)) (cokernel (D.adapter.etaMap b)) := rfl

theorem etaESS_page_differential {stable : StableHomotopyContext}
    {X Y : stable.Spectrum} {source : ClassicalAdamsSS stable X}
    {target : ClassicalAdamsSS stable Y} (D : EtaESSInput source target)
    (row : EtaDifferential) (hrow : row ∈ D.differentials) :
    ((etaESS D).page row.length).d row.sourceDegree row.targetDegree =
      D.adapter.rowMap row :=
  D.pageData.row row hrow

theorem etaESS_row_nonzero {stable : StableHomotopyContext}
    {X Y : stable.Spectrum} {source : ClassicalAdamsSS stable X}
    {target : ClassicalAdamsSS stable Y} (D : EtaESSInput source target)
    (row : EtaDifferential) (hrow : row ∈ D.differentials) :
    ((etaESS D).page row.length).d row.sourceDegree row.targetDegree ≠ 0 := by
  rw [etaESS_page_differential D row hrow]
  apply D.adapter.rowMap_nonzero
  have hClaim := D.ledgerEvidence.value.evidence
  change D.differentials = etaESSDifferentials at hClaim
  rw [hClaim] at hrow
  exact hrow

theorem extension_iff_detected {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) (row : EtaDifferential) :
    FExtension D row ↔ DetectedBy D row := by
  simp [FExtension, DetectedBy, D.detected_eq_differentials]

theorem differential_claim {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) :
    KIP126.Classical.Regression.etaEss D.differentials :=
  D.ledgerEvidence.value.evidence

theorem etaD₄_has_degree {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) :
    etaD₄ ∈ D.differentials :=
  by
    have h := differential_claim D
    change D.differentials = etaESSDifferentials at h
    rw [h]
    simp [etaESSDifferentials]

theorem etaD₁_has_locator :
    etaD₁.locator.artifact = some "aimpaper/main.tex" := rfl

theorem etaD₄_has_crossing {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) :
    Crossing D etaD₄ ↔ ∃ other, other ∈ D.differentials ∧
      other.sourceFiltration > etaD₄.sourceFiltration ∧
      other.targetFiltration ≤ etaD₄.targetFiltration := Iff.rfl

theorem etaD₄_crossing {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) : Crossing D etaD₄ := by
  have hClaim := differential_claim D
  change D.differentials = etaESSDifferentials at hClaim
  refine ⟨etaD₁, ?_, by decide, by decide⟩
  rw [hClaim]
  simp [etaESSDifferentials]

theorem etaD₁_noCrossing {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) : NoCrossing D etaD₁ := by
  have hClaim := differential_claim D
  change D.differentials = etaESSDifferentials at hClaim
  rw [NoCrossing, Crossing, hClaim]
  simp [etaESSDifferentials, etaD₁, etaD₂, etaD₃, etaD₄, etaD₂Inessential]

end KIP126.Classical.ExtensionSS
