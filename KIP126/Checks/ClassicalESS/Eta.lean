import KIP126.Def.ClassicalESS.Eta.Proofs

/-!
# Regression checks for the concrete classical eta-ESS
-/

namespace KIP126.Classical.ExtensionSS.Regression

open CategoryTheory CategoryTheory.Limits
open KIP126.Classical.Adams

example : etaESSPageLevel.firstPage = 0 := rfl
example (r : ℕ) : etaESSPageLevel.page r = r := rfl
example (r : ℕ) : etaESSPageLevel.cycleLevel r = r := rfl
example (r : ℕ) :
    etaESSPageLevel.quotientExponent r = etaESSPageLevel.page r := rfl

variable {stable : StableHomotopyContext} {X Y : stable.Spectrum}
  {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}

example (n : ℕ) : differentialDegree n = ((n : ℤ), (n : ℤ)) := by
  rfl

example (D : EtaESSInput source target) :
    E₀ D.adapter = fun b => D.adapter.sourceInfinity b ⊞
      D.adapter.targetInfinity b := rfl

example (D : EtaESSInput source target) (b : Index) :
    abutment D b = (kernel (D.adapter.etaMap b) ⊞ cokernel (D.adapter.etaMap b)) :=
  abutment_component D b

example (_D : EtaESSInput source target) (n : ℤ) (b : Index) :
    (etaESSShape n).Rel b (b + (n, n)) :=
  etaESSShape_rel n b

example (D : EtaESSInput source target) (row : EtaDifferential) :
    FExtension D row ↔ DetectedBy D row :=
  extension_iff_detected D row

example (D : EtaESSInput source target) :
    etaD₄ ∈ D.differentials :=
  etaD₄_has_degree D

example : etaD₁.locator.artifact = some "aimpaper/main.tex" :=
  etaD₁_has_locator

example (D : EtaESSInput source target) :
    Crossing D etaD₄ ↔ ∃ row, row ∈ D.differentials ∧
      row.sourceFiltration > etaD₄.sourceFiltration ∧
      row.targetFiltration ≤ etaD₄.targetFiltration :=
  etaD₄_has_crossing D

example (D : EtaESSInput source target) : Crossing D etaD₄ :=
  etaD₄_crossing D

example (D : EtaESSInput source target) : NoCrossing D etaD₁ :=
  etaD₁_noCrossing D

example (D : EtaESSInput source target) :
    KIP126.Classical.Regression.etaEss D.differentials :=
  differential_claim D

example (D : EtaESSInput source target) (row : EtaDifferential)
    (hrow : row ∈ D.differentials) :
    ((etaESS D).page row.length).d row.sourceDegree row.targetDegree =
      D.adapter.rowMap row :=
  etaESS_page_differential D row hrow

example (D : EtaESSInput source target) (row : EtaDifferential)
    (hrow : row ∈ D.differentials) :
    ((etaESS D).page row.length).d row.sourceDegree row.targetDegree ≠ 0 :=
  etaESS_row_nonzero D row hrow

example (D : EtaESSInput source target) :
    Essential D etaD₁ ∧ Essential D etaD₂ ∧ Essential D etaD₃ ∧
      Essential D etaD₄ ∧ ¬ Essential D etaD₂Inessential := by
  have hClaim := differential_claim D
  change D.differentials = etaESSDifferentials at hClaim
  simp [Essential, FExtension, hClaim, etaESSDifferentials, etaD₁, etaD₂,
    etaD₃, etaD₄, etaD₂Inessential]

example (D : EtaESSInput source target) (row : EtaDifferential) :
    (D.adapter.sourceClass row).degree = row.sourceDegree ∧
      (D.adapter.targetClass row).degree = row.targetDegree :=
  ⟨D.adapter.sourceClass_degree row, D.adapter.targetClass_degree row⟩

end KIP126.Classical.ExtensionSS.Regression
