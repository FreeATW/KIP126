import KIP126.External.SourceInventory
import KIP126.External.Evidence

/-!
# Source-inventory regression checks

These examples pin the finite completeness and JSON/Lean projection boundary
without importing the claim ledger.  Canonical locator membership, filesystem
existence, and checked-in-file digest matching remain external checks.
-/

namespace KIP126.External.SourceInventoryRegression

open KIP126.External

private def browderRef : SourceRef :=
  { source := .browder
    locator :=
      { description := "Browder regression locator"
        artifact := some "reference/Browder/paper.txt" } }

private def browderArtifact : ArtifactRef :=
  { path := "reference/Browder/paper.pdf"
    sha256 := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" }

private def browderResult : ExternalResult True :=
  { proof := True.intro, ref := browderRef }

private def browderEvidence : ExternalEvidence True :=
  { evidence := True.intro
    ref := browderRef
    method := "finite regression check"
    artifact := some browderArtifact }

private def traversalRef : SourceRef :=
  { source := .browder
    locator :=
      { description := "escaping locator"
        artifact := some "reference/Browder/../HHR/paper.txt" } }

private def traversalEvidence : ExternalEvidence True :=
  { evidence := True.intro
    ref := browderRef
    method := "malformed regression check"
    artifact := some
      { path := "reference/Browder/../HHR/paper.pdf"
        sha256 := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" } }

private def malformedHashEvidence : ExternalEvidence True :=
  { evidence := True.intro
    ref := browderRef
    method := "malformed digest regression"
    artifact := some
      { path := "reference/Browder/paper.pdf"
        sha256 := "not-a-sha256" } }

example :
    SourceInventory.inventory.entries.map SourceEntry.source = SourceId.all :=
  SourceInventory.inventory_complete

example : SourceInventory.inventory.entries.length = 18 :=
  SourceInventory.inventory_count

example (source : SourceId) :
    (SourceInventory.inventory.lookup source).Valid :=
  SourceInventory.inventory_valid source

example : SourceInventory.GloballyValid SourceInventory.inventory :=
  SourceInventory.inventory_globally_valid

example (ref : SourceRef) :
    (SourceInventory.resolve ref).source = ref.source :=
  SourceInventory.resolve_source ref

example (source : SourceId) :
    SourceInventory.resolveCode (SourceId.code source) =
      some (SourceInventory.inventory.lookup source) :=
  SourceInventory.resolveCode_code source

example : SourceInventory.resolveCode "not_a_kip126_source" = none := by
  rfl

example :
    SourceInventory.projection.map SourceInventory.SourceProjection.id = SourceId.all :=
  SourceInventory.projection_ids

example : SourceInventory.projection.length = SourceId.all.length :=
  SourceInventory.projection_complete

example : SourceInventory.projection.length = 18 := by
  simpa [SourceId.all_length] using SourceInventory.projection_complete

example :
    (SourceInventory.projection.map SourceInventory.SourceProjection.id).Nodup :=
  SourceInventory.projection_nodup

example :
    SourceEntry.pathHasDirectoryPrefix "reference/Browder"
      "reference/BrowderArchive/paper.pdf" = false := by
  decide

/-- Checkout-relative safety rejects both leading and internal traversal. -/
example : SourceEntry.isSafeRelativePath "../reference/Browder/paper.pdf" = false := by
  decide

example :
    SourceEntry.isSafeRelativePath "reference/Browder/../HHR/paper.pdf" = false := by
  decide

example : SourceEntry.isSafeRelativePath "/reference/Browder/paper.pdf" = false := by
  decide

example : SourceEntry.isSafeRelativePath "reference/Browder/pipe|name.pdf" = false := by
  decide

example : SourceEntry.isSafeRelativePath "   " = false := by
  decide

private def emSpace : String :=
  String.singleton ⟨0x2003, by decide⟩

private def noBreakSpace : String :=
  String.singleton ⟨0xA0, by decide⟩

private def lineSeparator : String :=
  String.singleton ⟨0x2028, by decide⟩

example : SourceEntry.isSafeRelativePath emSpace = false := by
  decide

example : SourceEntry.citationKeySafe noBreakSpace = false := by
  decide

example :
    SourceEntry.isSafeRelativePath ("reference/Browder/" ++ lineSeparator ++ "paper.pdf") =
      false := by
  decide

example : SourceEntry.citationKeySafe "Browder|drift" = false := by
  decide

example : SourceEntry.citationKeySafe "Browder,drift" = false := by
  decide

/-- Typed wrappers preserve the stronger source-relative inventory boundary. -/
example : browderRef.InventoryValid := by
  unfold SourceRef.InventoryValid SourceRef.Valid Locator.Valid
  unfold SourceInventory.locatorPathValid SourceInventory.locatorPathValidWith
  unfold browderRef
  decide

example : browderResult.InventoryValid := by
  unfold ExternalResult.InventoryValid ExternalResult.Valid SourceRef.Valid Locator.Valid
  unfold SourceInventory.locatorPathValid SourceInventory.locatorPathValidWith
  unfold browderResult browderRef
  decide

example : browderEvidence.InventoryValid := by
  unfold ExternalEvidence.InventoryValid ExternalEvidence.Valid ExternalEvidence.metadata
  unfold EvidenceMetadata.Valid SourceRef.Valid Locator.Valid ArtifactRef.Valid
  unfold ArtifactRef.ValidSha256 ArtifactRef.IsSha256
  unfold SourceInventory.locatorPathValid SourceInventory.locatorPathValidWith
  unfold SourceInventory.artifactPathValid SourceInventory.artifactPathValidWith
  unfold browderEvidence browderRef browderArtifact
  decide

/-- A structurally non-empty path is still rejected when it escapes its source
directory through a `..` component. -/
example : ¬traversalRef.InventoryValid := by
  unfold SourceRef.InventoryValid SourceRef.Valid Locator.Valid
  unfold SourceInventory.locatorPathValid SourceInventory.locatorPathValidWith
  unfold traversalRef
  decide

example : ¬traversalEvidence.InventoryValid := by
  unfold ExternalEvidence.InventoryValid ExternalEvidence.Valid ExternalEvidence.metadata
  unfold EvidenceMetadata.Valid SourceRef.Valid Locator.Valid ArtifactRef.Valid
  unfold ArtifactRef.ValidSha256 ArtifactRef.IsSha256
  unfold SourceInventory.locatorPathValid SourceInventory.locatorPathValidWith
  unfold SourceInventory.artifactPathValid SourceInventory.artifactPathValidWith
  unfold traversalEvidence browderRef
  decide

example : ¬malformedHashEvidence.InventoryValid := by
  unfold ExternalEvidence.InventoryValid ExternalEvidence.Valid ExternalEvidence.metadata
  unfold EvidenceMetadata.Valid SourceRef.Valid Locator.Valid ArtifactRef.Valid
  unfold ArtifactRef.ValidSha256 ArtifactRef.IsSha256
  unfold SourceInventory.locatorPathValid SourceInventory.locatorPathValidWith
  unfold SourceInventory.artifactPathValid SourceInventory.artifactPathValidWith
  unfold malformedHashEvidence browderRef
  decide

example :
    SourceStatusClass.classify .browder
      { metadata := false, pdf := false, text := false, source := false } =
      .partialAvailability := by
  decide

example : SourceEntry.citationKeysNonempty [] = false := by
  decide

example :
    ¬SourceEntry.Valid
      { source := .aimPaper
        kind := .paper
        citationKeys := ["LWX126"]
        directory := "aimpaper"
        statusFile := none
        statusClass := .sourceOfRecord
        availability :=
          { metadata := false, pdf := false, text := false, source := false } } := by
  simp [SourceEntry.Valid, SourceEntry.CitationKeysValid,
    SourceEntry.citationKeysNonempty, SourceEntry.citationKeySafe,
    SourceEntry.schemaCharSafe, SourceEntry.projectionLineSeparator,
    SourceEntry.KindConsistent,
    SourceEntry.StatusConsistent, SourceEntry.statusPathConsistent,
    SourceStatusClass.classify, SourceAvailability.all]

end KIP126.External.SourceInventoryRegression
