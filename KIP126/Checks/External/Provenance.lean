import KIP126.External

/-!
# Provenance API regression checks

This module exercises the public composition laws of the provenance kernel.
It contains no project-specific mathematical input and deliberately constructs
every proposition from an explicit local proof.
-/

namespace KIP126.External.ProvenanceRegression

private def locator : Locator :=
  { description := "regression theorem"
    artifact := some "reference/example/paper.txt" }

private def ref : SourceRef :=
  { source := .browder, locator := locator }

private def artifact : ArtifactRef :=
  { path := "reference/example/output.json"
    sha256 := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
    version := some "regression" }

example : locator.Valid := by
  exact Locator.valid_of_artifact _ _ (by decide) (by decide)

example : ref.Valid := by
  exact Locator.valid_of_artifact _ _ (by decide) (by decide)

example : artifact.Valid := by
  exact ⟨by decide, by decide⟩

example (source : SourceId) : SourceId.ofCode (SourceId.code source) = some source :=
  SourceId.ofCode_code source

example : SourceId.all.length = 18 := SourceId.all_length

example : SourceKind.all.length = 4 := SourceKind.all_length

example : SourceId.ofCode "not_a_kip126_source" = none := rfl

/-- Decoders are closed and case-sensitive: unknown source, kind, and status
codes never acquire a fallback constructor. -/
example : SourceId.ofCode "Browder" = none := rfl

example : SourceKind.ofCode "dataset" = none := rfl

example : SourceStatusClass.ofCode "unknown" = none := rfl

example (kind : SourceKind) : SourceKind.ofCode (SourceKind.code kind) = some kind :=
  SourceKind.ofCode_code kind

example (status : SourceStatusClass) :
    SourceStatusClass.ofCode (SourceStatusClass.code status) = some status :=
  SourceStatusClass.ofCode_code status

example {key : String} {source : SourceId}
    (h : SourceId.ofCode key = some source) : SourceId.code source = key := by
  exact SourceId.code_of_ofCode h

example {P : Prop} (result : ExternalResult P) :
    ExternalResult.map (fun proof => proof) result = result := by
  simp

example {P Q R : Prop} (f : P → Q) (g : Q → R)
    (result : ExternalResult P) :
    ExternalResult.map g (ExternalResult.map f result) =
      ExternalResult.map (fun proof => g (f proof)) result := by
  simp

example {P Q : Prop} (f : P → Q) (result : ExternalResult P) :
    (ExternalResult.map f result).Valid ↔ result.Valid := by
  simp

example {P : Prop} (evidence : ExternalEvidence P) :
    ExternalEvidence.map (fun proof => proof) evidence = evidence := by
  simp

example {P Q R : Prop} (f : P → Q) (g : Q → R)
    (evidence : ExternalEvidence P) :
    ExternalEvidence.map g (ExternalEvidence.map f evidence) =
      ExternalEvidence.map (fun proof => g (f proof)) evidence := by
  simp

example {P Q : Prop} (f : P → Q) (evidence : ExternalEvidence P) :
    (ExternalEvidence.map f evidence).Valid ↔ evidence.Valid := by
  simp

example {P : Prop} (evidence : ExternalEvidence P) :
    (ExternalEvidence.withArtifact evidence artifact).ref = evidence.ref ∧
      (ExternalEvidence.withArtifact evidence artifact).method = evidence.method ∧
      (ExternalEvidence.withArtifact evidence artifact).artifact = some artifact := by
  simp

example {P : Prop} (evidence : ExternalEvidence P) (hEvidence : evidence.Valid) :
    (ExternalEvidence.withArtifact evidence artifact).Valid := by
  exact ExternalEvidence.withArtifact_valid evidence artifact hEvidence
    (by exact ⟨by decide, by decide⟩)

/-- The inventory spelling accepts exactly 64 lower-case hexadecimal digits. -/
example :
    ArtifactRef.IsSha256
      "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" := by
  unfold ArtifactRef.IsSha256
  decide

/-- An upper-case hexadecimal digit is rejected even when the length is 64. -/
example :
    ¬ArtifactRef.IsSha256
      "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdeF" := by
  unfold ArtifactRef.IsSha256
  decide

example : artifact.ValidSha256 := by
  unfold ArtifactRef.ValidSha256
  constructor
  · decide
  · unfold ArtifactRef.IsSha256
    decide

end KIP126.External.ProvenanceRegression
