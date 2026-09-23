import KIP126.External.Computation.EtaRows.Data

/-!
# Regression checks for typed classical eta data
-/

namespace KIP126.Classical.ExtensionSS.EtaDataRegression

open KIP126.Classical.Adams
open KIP126.External

variable {stable : StableHomotopyContext} {X Y : stable.Spectrum}
  {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}

example : EtaRowId.all.length = 5 := by
  simp

example : Fintype.card EtaRowId = 5 := by
  decide

example : Set.range EtaRowId.row = etaESSDifferentials :=
  EtaRowId.range_row

example (id : EtaRowId) :
    id.row.locator.artifact = some "aimpaper/main.tex" := by
  cases id <;> rfl

example (data : EtaData source target) : data.eta.degree = (1, 2) :=
  data.eta_degree

example (data : EtaData source target) (id : EtaRowId) :
    (data.sourceClass id).degree = id.row.sourceDegree ∧
      (data.targetClass id).degree = id.row.targetDegree :=
  ⟨data.sourceClass_degree id, data.targetClass_degree id⟩

example (data : EtaData source target) :
    data.ledgerEvidence.root = .etaEssRegression :=
  data.ledger_root_eq

example (data : EtaData source target) :
    KIP126.Classical.Regression.etaEss etaESSDifferentials :=
  data.ledger_claim

/-- info: 'KIP126.Classical.ExtensionSS.EtaRowId.range_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms EtaRowId.range_row

/-- info: 'KIP126.Classical.ExtensionSS.EtaTypedRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EtaTypedRow

/-- info: 'KIP126.Classical.ExtensionSS.EtaData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EtaData

/-- info: 'KIP126.Classical.ExtensionSS.EtaData.sourceClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EtaData.sourceClass

/-- info: 'KIP126.Classical.ExtensionSS.EtaData.targetClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EtaData.targetClass

/-- info: 'KIP126.Classical.ExtensionSS.EtaData.sourceClass_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EtaData.sourceClass_degree

/-- info: 'KIP126.Classical.ExtensionSS.EtaData.targetClass_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EtaData.targetClass_degree

/-- info: 'KIP126.Classical.ExtensionSS.EtaData.ledger_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EtaData.ledger_claim

/-- info: 'KIP126.Classical.ExtensionSS.EtaData.ledger_root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EtaData.ledger_root_eq

end KIP126.Classical.ExtensionSS.EtaDataRegression
