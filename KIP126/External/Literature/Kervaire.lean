import KIP126.Def.Kervaire.Theta5.Predicates
import KIP126.External.Claims

/-!
# Located Kervaire literature interfaces

This module keeps source results separate from the project deductions.  Each
constructor below requires the proposition supplied by a caller and attaches
the matching canonical claim row.  There is no global witness and no theorem
that turns a source identifier into a proposition.
-/

namespace KIP126.Kervaire

open KIP126.External

section Theta5

variable {Carrier : Type} [AddCommGroup Carrier]
variable (C : Theta5ChoiceContext (Carrier := Carrier))

/-- A BJM/BX result attached to the canonical Burklund--Xu claim row. -/
def cataloguedBJM_BXCriterion (proof : BJM_BXCriterion C) :
    CataloguedExternalResult (BJM_BXCriterion C) :=
  { root := .bjmBxCriterion
    value :=
      { proof := proof
        ref := (externalClaimLedger.lookup .bjmBxCriterion).ref }
    ref_eq := rfl
    class_supported := by trivial }

@[simp] theorem cataloguedBJM_BXCriterion_source
    (proof : BJM_BXCriterion C) :
    (cataloguedBJM_BXCriterion C proof).value.ref.source =
      SourceId.burklundXu := by
  rfl

/-- The Xu/IWX order and choice-comparison result attached to its composite
claim row. -/
def cataloguedTheta5OrderData (proof : Theta5OrderData C) :
    CataloguedExternalResult (Theta5OrderData C) :=
  { root := .theta5OrderData
    value :=
      { proof := proof
        ref := (externalClaimLedger.lookup .theta5OrderData).ref }
    ref_eq := rfl
    class_supported := by trivial }

@[simp] theorem cataloguedTheta5OrderData_source
    (proof : Theta5OrderData C) :
    (cataloguedTheta5OrderData C proof).value.ref.source =
      SourceId.aimPaper := by
  rfl

/-- The total differential identity attached to the located Burklund--Xu
construction. -/
def cataloguedTotalDifferentialIdentity (proof : TotalDifferentialIdentity C) :
    CataloguedExternalResult (TotalDifferentialIdentity C) :=
  { root := .totalDifferentialIdentity
    value :=
      { proof := proof
        ref := (externalClaimLedger.lookup .totalDifferentialIdentity).ref }
    ref_eq := rfl
    class_supported := by trivial }

@[simp] theorem cataloguedTotalDifferentialIdentity_source
    (proof : TotalDifferentialIdentity C) :
    (cataloguedTotalDifferentialIdentity C proof).value.ref.source =
      SourceId.burklundXu := by
  rfl

/-- The finite evidence wrapper for the order/torsion computation.  The
artifact and its digest remain fields of `CataloguedExternalEvidence`; this
constructor intentionally leaves them to the evidence producer. -/
abbrev Theta5OrderTorsionInput : Type :=
  CataloguedExternalEvidence (Theta5OrderTorsionEvidence C)

/-- Build an evidence wrapper with no artifact yet.  The source-relative
locator and inventory path are still checked against the canonical claim row;
an archive artifact can be attached later with `ExternalEvidence.withArtifact`.
-/
def cataloguedTheta5OrderTorsion
    (proof : Theta5OrderTorsionEvidence C)
    (method : String) (hMethod : method ≠ "") :
    CataloguedExternalEvidence (Theta5OrderTorsionEvidence C) :=
  { root := .theta5OrderTorsion
    value :=
      { evidence := proof
        ref := (externalClaimLedger.lookup .theta5OrderTorsion).ref
        method := method
        artifact := none }
    ref_eq := rfl
    class_supported := by trivial
    inventory_valid := by
      have hRef := ExternalClaimRecord.ref_inventoryValid_of_valid
        (externalClaimLedger.lookup .theta5OrderTorsion)
        (externalClaimLedger_valid .theta5OrderTorsion)
      exact ⟨⟨hRef.1, ⟨hMethod, trivial⟩⟩, hRef.2, trivial⟩
    artifact_compatible := by trivial }

end Theta5

section PublishedGeometry

variable {Manifold : Type}
variable (dimension : Manifold → ℕ)
variable (kervaireOne : Manifold → Prop)
variable (permanent : ℕ → Prop)

/-- Browder's criterion with the exact source locator from the claim ledger. -/
def cataloguedBrowderCriterion
    (proof : BrowderCriterionStatement dimension kervaireOne permanent) :
    CataloguedExternalResult
      (BrowderCriterionStatement dimension kervaireOne permanent) :=
  { root := .browderCriterion
    value :=
      { proof := proof
        ref := (externalClaimLedger.lookup .browderCriterion).ref }
    ref_eq := rfl
    class_supported := by trivial }

@[simp] theorem cataloguedBrowderCriterion_source
    (proof : BrowderCriterionStatement dimension kervaireOne permanent) :
    (cataloguedBrowderCriterion dimension kervaireOne permanent proof).value.ref.source =
      SourceId.browder := by
  rfl

/-- HHR's nonexistence statement with its own canonical source row. -/
def cataloguedHHRNonexistence
    (proof : HHRNonexistenceStatement dimension kervaireOne) :
    CataloguedExternalResult (HHRNonexistenceStatement dimension kervaireOne) :=
  { root := .hhrNonexistence
    value :=
      { proof := proof
        ref := (externalClaimLedger.lookup .hhrNonexistence).ref }
    ref_eq := rfl
    class_supported := by trivial }

@[simp] theorem cataloguedHHRNonexistence_source
    (proof : HHRNonexistenceStatement dimension kervaireOne) :
    (cataloguedHHRNonexistence dimension kervaireOne proof).value.ref.source =
      SourceId.hhr := by
  rfl

end PublishedGeometry

section BJMInduction

variable {Class : Type}
variable (detected : ℕ → Class → Prop)
variable (isOrderTwo : Class → Prop)
variable (squareZero : Class → Prop)

/-- The BJM induction input attached to the dedicated claim row. -/
def cataloguedBJMInduction
    (proof : BJMInductionStatement detected isOrderTwo squareZero) :
    CataloguedExternalResult
      (BJMInductionStatement detected isOrderTwo squareZero) :=
  { root := .bjmInduction
    value :=
      { proof := proof
        ref := (externalClaimLedger.lookup .bjmInduction).ref }
    ref_eq := rfl
    class_supported := by trivial }

@[simp] theorem cataloguedBJMInduction_source
    (proof : BJMInductionStatement detected isOrderTwo squareZero) :
    (cataloguedBJMInduction detected isOrderTwo squareZero proof).value.ref.source =
      SourceId.bjmInduction := by
  rfl

end BJMInduction

end KIP126.Kervaire
