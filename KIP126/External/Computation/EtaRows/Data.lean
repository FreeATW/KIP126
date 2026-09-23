import KIP126.Def.ClassicalESS.Eta.Data
import KIP126.External.Claims

/-!
# Typed data for the classical eta extension spectral sequence

This module isolates the finite, source-backed Adams data used to construct
the classical eta-ESS.  It intentionally contains no eta map, row map, page
differential, or nonvanishing witness; those belong to the downstream
construction.
-/

namespace KIP126.Classical.ExtensionSS

open KIP126.Classical.Adams
open KIP126.External

/-- Stable identities for the five rows in the eta-ESS regression table. -/
inductive EtaRowId
  | d₁
  | d₂
  | d₃
  | d₄
  | d₂Inessential
  deriving DecidableEq, Repr, Inhabited

namespace EtaRowId

/-- The canonical existing differential selected by a stable row identity. -/
def row : EtaRowId → EtaDifferential
  | .d₁ => etaD₁
  | .d₂ => etaD₂
  | .d₃ => etaD₃
  | .d₄ => etaD₄
  | .d₂Inessential => etaD₂Inessential

/-- The five row identities in their canonical table order. -/
def all : List EtaRowId := [.d₁, .d₂, .d₃, .d₄, .d₂Inessential]

@[simp] theorem all_length : all.length = 5 := rfl

@[simp] theorem mem_all (id : EtaRowId) : id ∈ all := by
  cases id <;> simp [all]

/-- The row identities form a closed finite type. -/
instance : Fintype EtaRowId where
  elems := {.d₁, .d₂, .d₃, .d₄, .d₂Inessential}
  complete id := by cases id <;> simp

/-- Every stable identity selects a row in the existing eta-ESS catalogue. -/
theorem row_mem_etaESSDifferentials (id : EtaRowId) :
    id.row ∈ etaESSDifferentials := by
  cases id <;> simp [row, etaESSDifferentials]

/-- The stable identities enumerate exactly the existing five-row catalogue. -/
theorem range_row : Set.range row = etaESSDifferentials := by
  ext differential
  constructor
  · rintro ⟨id, rfl⟩
    exact row_mem_etaESSDifferentials id
  · intro h
    simp only [etaESSDifferentials, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h
    · exact ⟨.d₁, h.symm⟩
    · exact ⟨.d₂, h.symm⟩
    · exact ⟨.d₃, h.symm⟩
    · exact ⟨.d₄, h.symm⟩
    · exact ⟨.d₂Inessential, h.symm⟩

end EtaRowId

/-- Typed Adams representatives for one canonically identified eta-ESS row. -/
structure EtaTypedRow {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y)
    (id : EtaRowId) where
  sourceClass : AdamsClass source
  targetClass : AdamsClass target
  sourceClass_degree : sourceClass.degree = id.row.sourceDegree
  targetClass_degree : targetClass.degree = id.row.targetDegree

/-- Complete upstream data for the classical eta-ESS construction.

The source and target Adams systems are fixed by the structure parameters.
Rows can only be requested through `EtaRowId`, so callers cannot inject an
uncatalogued row.  The evidence is tied to the existing eta regression root. -/
structure EtaData {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y) where
  eta : AdamsClass source
  eta_degree : eta.degree = (1, 2)
  typedRow : (id : EtaRowId) → EtaTypedRow source target id
  ledgerEvidence : CataloguedExternalEvidence
    (KIP126.Classical.Regression.etaEss etaESSDifferentials)
  ledger_root : ledgerEvidence.root = .etaEssRegression

namespace EtaData

variable {stable : StableHomotopyContext} {X Y : stable.Spectrum}
  {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}

/-- The typed source representative of a canonical row. -/
def sourceClass (data : EtaData source target) (id : EtaRowId) :
    AdamsClass source :=
  (data.typedRow id).sourceClass

/-- The typed target representative of a canonical row. -/
def targetClass (data : EtaData source target) (id : EtaRowId) :
    AdamsClass target :=
  (data.typedRow id).targetClass

@[simp] theorem sourceClass_degree (data : EtaData source target)
    (id : EtaRowId) :
    (data.sourceClass id).degree = id.row.sourceDegree :=
  (data.typedRow id).sourceClass_degree

@[simp] theorem targetClass_degree (data : EtaData source target)
    (id : EtaRowId) :
    (data.targetClass id).degree = id.row.targetDegree :=
  (data.typedRow id).targetClass_degree

/-- The evidence carried by the payload proves the canonical five-row claim. -/
theorem ledger_claim (data : EtaData source target) :
    KIP126.Classical.Regression.etaEss etaESSDifferentials :=
  data.ledgerEvidence.value.evidence

/-- The payload's evidence uses the pre-existing eta-ESS catalogue root. -/
theorem ledger_root_eq (data : EtaData source target) :
    data.ledgerEvidence.root = .etaEssRegression :=
  data.ledger_root

end EtaData

end KIP126.Classical.ExtensionSS
