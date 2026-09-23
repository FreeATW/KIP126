import KIP126.External.Claims

/-!
# Claim-ledger regression checks

Small checks for the finite claim manifest and its connection to the document
inventory.  The `#print axioms` commands make kernel dependencies visible in
the build log.
-/

namespace KIP126.External.ClaimsRegression

private def browderResult : ExternalResult True :=
  { proof := True.intro
    ref := (externalClaimLedger.lookup .browderCriterion).ref }

private def cataloguedBrowderResult : CataloguedExternalResult True :=
  { root := .browderCriterion
    value := browderResult
    ref_eq := rfl
    class_supported := by trivial }

private def machineEvidence : ExternalEvidence True :=
  { evidence := True.intro
    ref := (externalClaimLedger.lookup .linMachineRelease).ref
    method := "checked machine-release regression"
    artifact := none }

private theorem machineEvidence_inventoryValid : machineEvidence.InventoryValid := by
  obtain ⟨hRef, hPath⟩ :=
    ExternalClaimRecord.ref_inventoryValid_of_valid
      (externalClaimLedger.lookup .linMachineRelease)
      (externalClaimLedger_valid .linMachineRelease)
  unfold machineEvidence ExternalEvidence.InventoryValid ExternalEvidence.Valid
  unfold ExternalEvidence.metadata EvidenceMetadata.Valid
  exact ⟨⟨hRef, by exact ⟨by decide, trivial⟩⟩, hPath, trivial⟩

private def cataloguedMachineEvidence : CataloguedExternalEvidence True :=
  { root := .linMachineRelease
    value := machineEvidence
    ref_eq := rfl
    class_supported := by trivial
    inventory_valid := machineEvidence_inventoryValid
    artifact_compatible := by trivial }

private def malformedOwnerClaim : ExternalClaimRecord :=
  { externalClaimLedger.lookup .browderCriterion with
    owner := `Unrelated.Project.claim }

private def malformedTargetClaim : ExternalClaimRecord :=
  { externalClaimLedger.lookup .browderCriterion with
    target := "unstable-target" }

private def malformedClassificationClaim : ExternalClaimRecord :=
  { externalClaimLedger.lookup .browderCriterion with
    classification := .machineEvidence }

private def malformedSelfDependencyClaim : ExternalClaimRecord :=
  { externalClaimLedger.lookup .browderCriterion with
    dependencies := [.browderCriterion] }

private def malformedDuplicateDependencyClaim : ExternalClaimRecord :=
  { externalClaimLedger.lookup .adamsOneLine with
    dependencies := [.mayLowPageSurvival, .mayLowPageSurvival] }

private def projectionLineSeparator : String :=
  String.singleton ⟨0x2028, by decide⟩

private def malformedProjectionOwnerClaim : ExternalClaimRecord :=
  { externalClaimLedger.lookup .browderCriterion with
    owner := Lean.Name.mkStr (Lean.Name.mkSimple "KIP126")
      ("BadOwner" ++ projectionLineSeparator) }

private def malformedProjectionTargetClaim : ExternalClaimRecord :=
  { externalClaimLedger.lookup .browderCriterion with
    target := "thm:external-browder-criterion" ++ projectionLineSeparator ++
      "NOT_THE_TARGET" }

private def mismatchedMachineArtifact : ArtifactRef :=
  { path := "reference/LWXMachine/paper.pdf"
    sha256 := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" }

example :
    externalClaimLedger.entries.map ExternalClaimRecord.id = ExternalRootId.all :=
  externalClaimLedger_complete

example : (externalClaimLedger.entries.map ExternalClaimRecord.id).Nodup :=
  externalClaimLedger_nodup

example : externalClaimLedger.entries.length = 56 :=
  externalClaimLedger_count

example (root : ExternalRootId) : (externalClaimLedger.lookup root).Valid :=
  externalClaimLedger_valid root

example (source : SourceId) :
    ∃ root, (externalClaimLedger.lookup root).ref.source = source :=
  every_source_has_claim source

example (classification : ExternalClaimClass) :
    ExternalClaimClass.ofCode (ExternalClaimClass.code classification) =
      some classification :=
  ExternalClaimClass.ofCode_code classification

example (root : ExternalRootId) :
    ExternalRootId.ofCode (ExternalRootId.code root) = some root :=
  ExternalRootId.ofCode_code root

example : ExternalRootId.all.length = 56 := ExternalRootId.all_length

example : ExternalClaimRecord.sourceTargets.length = 9 :=
  ExternalClaimRecord.sourceTargets_length

example : ExternalClaimClass.all.length = 5 := ExternalClaimClass.all_length

example : ExternalRootId.ofCode "not_a_claim" = none := by
  rfl

example : ExternalRootId.ofCode "Browder_Criterion" = none := rfl

example : ExternalClaimClass.ofCode "unknown" = none := rfl

example : ExternalClaimLedger.DependencyAcyclic externalClaimLedger :=
  externalClaimLedger_dependency_acyclic

example : ExternalClaimLedger.NoDependencyCycle externalClaimLedger :=
  externalClaimLedger_no_dependency_cycle

example : externalClaimLedger.owners.Nodup :=
  externalClaimLedger_owners_nodup

example : externalClaimLedger.targets.Nodup :=
  externalClaimLedger_targets_nodup

example : externalClaimLedger.refs.Nodup :=
  externalClaimLedger_refs_nodup

example :
    externalClaimProjection.map ExternalClaimProjection.id = ExternalRootId.all :=
  externalClaimProjection_ids

example : externalClaimProjection.length = 56 :=
  externalClaimProjection_count

example :
    (externalClaimLedger.lookup .higherLambdaQuotientAlgebra).target =
      "source:higher-lambda-quotient-algebra-tower" := by
  rfl

example :
    (externalClaimLedger.lookup .higherLambdaQuotientAlgebra).ref.source =
      .burklundXu := by
  rfl

example :
    (externalClaimLedger.lookup .symmetricMonoidalDeformation).target =
      "source:symmetric-monoidal-deformation-construction" := by
  rfl

/-- The opaque BJM/BX criterion does not acquire the commutative-algebra tower
as a project proof dependency. -/
example :
    (externalClaimLedger.lookup .bjmBxCriterion).dependencies =
      [.bjmInduction] := by
  rfl

example (root : ExternalRootId) :
    resolveClaimCode (ExternalRootId.code root) =
      some (externalClaimLedger.lookup root) :=
  resolveClaimCode_code root

example : resolveClaimCode "not_a_claim" = none := rfl

/-- The result wrapper derives inventory validity from the canonical claim row. -/
example : cataloguedBrowderResult.value.InventoryValid :=
  CataloguedExternalResult.inventoryValid cataloguedBrowderResult

/-- Evidence wrappers carry the stronger certificate as a required field. -/
example : cataloguedMachineEvidence.value.InventoryValid :=
  cataloguedMachineEvidence.inventory_valid

/-- A catalogued evidence artifact cannot silently replace the claim
locator's canonical artifact path. -/
example :
    ¬(externalClaimLedger.lookup .linMachineRelease).ArtifactCompatible
      (some mismatchedMachineArtifact) := by
  unfold ExternalClaimRecord.ArtifactCompatible mismatchedMachineArtifact
  decide

/-- Malformed owner, target, classification, self-dependency, and duplicated
dependency rows are all rejected by `ExternalClaimRecord.Valid`. -/
example : ¬malformedOwnerClaim.Valid := by
  intro h
  have hOwner := h.1
  have hRejected : ¬malformedOwnerClaim.OwnerConsistent := by
    unfold malformedOwnerClaim ExternalClaimRecord.OwnerConsistent
    decide
  exact hRejected hOwner

example : ¬malformedProjectionOwnerClaim.Valid := by
  intro h
  have hOwner := h.1
  have hRejected : ¬malformedProjectionOwnerClaim.OwnerConsistent := by
    unfold malformedProjectionOwnerClaim ExternalClaimRecord.OwnerConsistent
    unfold ExternalClaimRecord.nameProjectionSafe SourceEntry.projectionFieldSafe
      SourceEntry.schemaCharSafe SourceEntry.projectionLineSeparator
    decide
  exact hRejected hOwner

example : ¬malformedTargetClaim.Valid := by
  intro h
  have hTarget := h.2.2.2.1
  have hRejected : ¬malformedTargetClaim.TargetConsistent := by
    unfold malformedTargetClaim ExternalClaimRecord.TargetConsistent
    decide
  exact hRejected hTarget

example : ¬malformedProjectionTargetClaim.Valid := by
  intro h
  have hTarget := h.2.2.2.1
  have hRejected : ¬malformedProjectionTargetClaim.TargetConsistent := by
    unfold malformedProjectionTargetClaim ExternalClaimRecord.TargetConsistent
    unfold SourceEntry.projectionFieldSafe SourceEntry.schemaCharSafe
      SourceEntry.projectionLineSeparator
    decide
  exact hRejected hTarget

example : ¬malformedClassificationClaim.Valid := by
  intro h
  have hClassification := h.2.2.2.2.1
  have hRejected : ¬malformedClassificationClaim.ClassificationConsistent := by
    unfold malformedClassificationClaim ExternalClaimRecord.ClassificationConsistent
    decide
  exact hRejected hClassification

example : ¬malformedSelfDependencyClaim.Valid := by
  intro h
  have hSelf := h.2.2.2.2.2.2.1
  have hMember :
      malformedSelfDependencyClaim.id ∈ malformedSelfDependencyClaim.dependencies := by
    unfold malformedSelfDependencyClaim
    decide
  exact hSelf hMember

example : ¬malformedDuplicateDependencyClaim.Valid := by
  intro h
  have hNodup := h.2.2.2.2.2.1
  have hRejected : ¬malformedDuplicateDependencyClaim.dependencies.Nodup := by
    unfold malformedDuplicateDependencyClaim
    decide
  exact hRejected hNodup

end KIP126.External.ClaimsRegression
