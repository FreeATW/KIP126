# KIP-base migration into KIP126

This migration preserves the complete KIP-base working tree and ports its active
library from Lean/mathlib 4.28.0 to KIP126's pinned 4.32.2 environment. The source
is commit `bff9a8d` plus the uncommitted `Crossing.lean` and
`FilteredComplex.lean` changes. In particular, the new differential relations,
crossing definitions, and lift statements are included, not just the Git HEAD.
`source-manifest.json` records the full commit ID and working-tree status.

## Coverage and recovery

- All 21 original Lean modules are under `KIPBase.lean` and `KIPBase/`, retain
  their names, and are included in the `KIPBase` Lake library's explicit glob.
- All 73 tracked files have an entry in `source-manifest.json`. Non-Lean
  material is preserved byte-for-byte under `original/`: all informal notes,
  references, original Blueprint sources, configuration and workflows.
  These old settings and workflows are reference material, not active settings.
- `source-4.28.tar.gz` preserves the exact working versions of all 73 tracked
  files, including uncommitted code changes; it is the versioned comparison base.
- `local/working-tree-4.28.tar.gz` preserves all 1,475 files outside `.git`, `.lake`
  and Python bytecode caches, including ignored `.archon` reports, proof
  snapshots, task history, local configuration, generated Blueprint output,
  and reference-paper build output. `local/snapshot-manifest.json` checks every
  byte. This complete backup is retained in the local migration checkout and is
  Git-ignored: the public PR does not publish untracked agent logs or connection
  settings. Copy the `local/` directory separately when moving this full backup.
- `history.bundle` preserves the source repository's Git refs/history. The
  working-tree archive, rather than the bundle, contains the latest uncommitted
  changes. The source checkout is left untouched.

To inspect historical material without enabling its local tool configuration:

```bash
tar -tzf migration/kip-base/source-4.28.tar.gz
tar -xOf migration/kip-base/local/working-tree-4.28.tar.gz .archon/PROGRESS.md
git bundle verify migration/kip-base/history.bundle
```

`python3 scripts/kipbase-migration.py` verifies the versioned source snapshot, the
byte-identical supporting material, and retention of every named source
declaration. This is a preservation check; compilation and the environment audit
provide separate typechecking and proof-dependency evidence.
Add `--full-snapshot` to verify all 1,475 locally backed-up files as well.
`port.patch` exposes only the changes made to the original Lean files, so review
does not require comparing thousands of newly added source lines manually.
Regenerate it with `--write-port-diff` after changing a historical source file.

## Trust boundary

The user explicitly authorized preservation of the inherited assumptions in an
isolated historical component during this migration. This exception is solely
for archival/compatibility retention; it does not relax `PROJECT_BOUNDARY.md`
for the `KIP126` formalization or certify any inherited assertion.

The source has **94 project axioms and 12 `sorry` occurrences**.
`trust-ledger.json` identifies their source modules, declaration names and
original line numbers. Some are definitions of data using `sorry`, not just
missing theorem proofs. Compilation success therefore does not mean a complete
formalization. No new `axiom`, `sorry`, or `admit` is permitted by the migration
checker. Every compatibility declaration must have only foundational axiom
dependencies; `scripts/KIPBaseAudit.lean` checks the compiled environment.

`KIP126` must not import any `KIPBase` module. The existing trusted axiom audit
now also rejects that import boundary crossing. Its foundational allowlist is
unchanged. To reuse a result in the paper's trusted proof chain, port it to the
canonical Mathlib/KIP126 objects, prove it there, and run the ordinary audit.
Literature inputs must go through `KIP126/External`; a theorem from this paper
cannot be treated as an external input just to remove a placeholder.

Keep particular care around the unproved `differentialRelation_crossed_of_two`
statement (its prose mentions distinct targets but its hypotheses do not), and
`finite_spectra_char` (the original axiom equates finiteness with `True`). They
are preserved for review, not endorsed. Similarly, `HF2_pin_zero` uses `IsEmpty`
for an additive group, where vanishing should describe a trivial group; this
is a substantive statement issue, not a version-compatibility fix.
The migration does not silently rewrite
their mathematical statements or replace the old ESS commutativity axioms by
the newer relation vocabulary.

## Mapping to aimpaper

| Historical modules | Intended paper role | Canonical destination / remaining work |
| --- | --- | --- |
| `SpectralSequence.Basic`, `Convergence` | Spectral-sequence and abutment foundations used throughout | `Core/SpectralSequence`; compare to Mathlib's authoritative model before reusing the nested-subobject presentation |
| `SpectralSequence.FilteredComplex`, `Crossing` | Filtered representatives, differentials and crossings for Section 2 and later extension arguments | `Core/SpectralSequence/FilteredComplex`, `FilteredRepresentatives`, `Classical/ExtensionSS`; five lift statements remain unfinished |
| `SpectralSequence.Truncation`, `Completion` | Unbounded filtrations and completion machinery supporting ESS | `Core/Algebra/Completion`, `Core/SpectralSequence/Convergence`; preserve proved truncation/completion lemmas |
| `SpectralSequence.BoundedExtension`, `UnboundedExtension` | Section 2 ESS construction (`def:ess`) and convergence | `Classical/ExtensionSS`; the legacy ESS accessors and convergence contain explicit proof debt |
| `SpectralSequence.Commutativity` | Section 2 ESS naturality/composition; inputs to Sections 5–6 | `Classical/PageExtensions`, `Comparison/ClassicalSynthetic`; 21 original axioms require proofs and statement alignment |
| `StableHomotopy.TensorTriangulatedCategory`, `Basic` | Stable homotopy background, cofibers and smash products | Shared stable context in the Blueprint; keep structural laws explicit and literature provenance separate |
| `StableHomotopy.Cohomology`, `Adams` | Classical Adams/cohomology foundations, filtration, convergence | `Classical/Adams`, `External`; distinguish external literature from unfinished constructions |
| `Synthetic.Basic`, `Sphere`, `Nu` | Section 3 HF₂-synthetic category, spheres, ν | `Synthetic`, `External`; preserve all original bigrading and λ-action conventions |
| `Synthetic.Adams`, `Rigidity` | Section 3 synthetic Adams and BHS rigidity (`thm:rigid`) | `Synthetic/Adams`, `Synthetic/Rigidity`, `External` provenance-carrying inputs |
| `Synthetic.Lift` | Section 3 synthetic lift (`not:fhat`), supporting Sections 4–6 | `Synthetic/ExtensionSS`, `Comparison/ClassicalSynthetic`; six inherited axioms remain explicit |
| `Basic`, root import | Whole historical library | Aggregate compatibility build, not a paper-completion theorem |

The retained material supplies foundations and draft statements for the paper;
it does not already contain proofs of all Sections 4–7 or the Appendix. The
existing `aimpaper/`, canonical Blueprint, and Appendix inventory remain the
authoritative project sources. Historical Blueprint annotations under
`original/` are retained as evidence of past intent, not current completion flags.

`KIPBase.Compatibility.FilteredComplex` supplies equivalences of the two
filtration and bounded-filtration structures, a conversion from the canonical
filtered chain complex to the historical API, and a conversion of historical
data to a Mathlib chain complex with its canonical KIP126 filtration.
It proves agreement of associated graded objects,
projections, differentials and the lift predicate, and transfers the old proved
square-zero lemma. It does not assert that the two spectral-sequence models are
equivalent at all pages or share an abutment.

## Compatibility changes

The active pins in `lean-toolchain` and `lake-manifest.json` are unchanged from
KIP126 main. The historical library has its original Lean options plus the
4.32 elaborator compatibility options `backward.defeqAttrib.useBackward = true`
and `backward.isDefEq.respectTransparency = false`. These are confined to the
`KIPBase` library and do not change kernel checking or the canonical library.

Unrestricted `import Mathlib` directives are replaced by the required category
theory, homological algebra, algebra and tactic modules. Local proof adaptations
handle extra definitional-equality goals produced by `convert`, remove an empty
`simp` step, and use the limit-projection naturality equation directly. All
389 named original declarations are retained. Mathematical statements and
inherited proof placeholders are preserved; the exact changes are in `port.patch`.

## Validation

The completed migration's counts and check results are recorded in
[VALIDATION.md](VALIDATION.md).

Use the repository's cache wrapper in an independent checkout:

```bash
bash scripts/shared-main-cache.sh run lake build KIPBase.Compatibility.FilteredComplex
bash scripts/shared-main-cache.sh run lake build
bash scripts/shared-main-cache.sh run lake env lean --run scripts/Axioms.lean
bash scripts/shared-main-cache.sh run lake exe kipbaseAudit > /tmp/kipbase-audit.json
python3 scripts/kipbase-migration.py --audit-report /tmp/kipbase-audit.json
```

The default build covers both libraries, including modules not imported by an
aggregate root. `scripts/euler-ci.sh` runs both audits and the preservation check.
Build-input cache keys include `KIPBase` sources. The existing PR sandbox treats
Lake/configuration changes as requiring human review; this migration must not
weaken that gate or claim an automatic merge-ready result.

The canonical gate remains `lake build KIP126 --iofail`. The historical target
uses `lake build KIPBase`, retaining visible warnings for its inventoried
placeholders and original style issues. A combined `lake build --iofail` would
necessarily reject those authorized historical warnings; the canonical warning
policy and proof audit have not been weakened. Byte-identical historical text
and unified-diff context are exempt from whitespace formatting checks only.
