# KIP126

## Dependencies

**Fixed Lean toolchain: `leanprover/lean4:v4.32.2`.** Both the canonical
`KIP126` library and the migrated `KIPBase` component use this toolchain with
mathlib **`v4.32.2`**. The authoritative pin is [`lean-toolchain`](lean-toolchain);
run Lake commands from this repository so Elan selects that exact version.

KIP126 is developed with the following projects and tools:

- [Lean](https://leanprover.github.io/) `4.32.2`, selected by
  [`lean-toolchain`](lean-toolchain);
- [Lake](https://github.com/leanprover/lake), the Lean package manager and
  build tool, configured in [`lakefile.lean`](lakefile.lean);
- [Mathlib](https://github.com/leanprover-community/mathlib4/) `v4.32.2`,
  pinned in [`lakefile.lean`](lakefile.lean);
- [Lean Blueprint](https://github.com/PatrickMassot/leanblueprint), exposed by
  the `leanblueprint` command for the natural-language formalization graph and
  its PDF, web, and declaration-check outputs;
- Python 3 for repository audits and regression checks under `scripts/`;
- a LaTeX toolchain with `latexmk` for Blueprint PDF generation.

The Lean and Mathlib versions must remain aligned. Blueprint's generated
directories (`blueprint/print` and `blueprint/web`) are ignored build outputs.
`blueprint/lean_decls` is likewise generated and ignored rather than hand-edited;
commands that consume it must run `leanblueprint web` first. CI preserves the
generated declaration list in the Blueprint artifact when it is needed later.

Lean 4.32.2 project and source-grounded Blueprint for the KIP126
formalization.

The complete historical KIP-base library is retained as the separately compiled
`KIPBase` component on the same Lean/mathlib 4.32.2 pins. Its original assumptions
are isolated from `KIP126` and do not count as completed paper proofs. See the
[migration inventory, paper mapping, and validation commands](migration/kip-base/README.md).

## Project documents and workflow

The repository assigns different questions to different authoritative sources;
this is a responsibility map rather than one document overriding every other
document:

- [`aimpaper/`](aimpaper/) contains the target paper and its source material.
  It is the mathematical document to be formalized; its claims are not, by
  themselves, Lean proofs or project theorems.
- [`PROJECT_BOUNDARY.md`](PROJECT_BOUNDARY.md) defines what this project does
  and does not formalize, together with its source, trust, and acceptance
  boundaries.
- [`docs/ROADMAP.md`](docs/ROADMAP.md) owns the long-term stages and dependency
  order: audit the earlier repositories and form KIP126's best-progress
  envelope, continue the chapter-level formalization, and finish with a
  repository-wide trust, provenance, completeness, and reproducibility audit.
- [`blueprint/src/content.tex`](blueprint/src/content.tex) and the chapters
  under [`blueprint/src/chapters`](blueprint/src/chapters) form the
  natural-language formalization sketch.  The Blueprint follows the paper's
  definitions and the roadmap's order, and refines each step into nodes whose
  mathematical statement, dependencies, sources, and intended Lean object can
  be checked together.  A chapter indexes several small Lean modules under
  `KIP126/Def/`, `KIP126/External/`, and `KIP126/Challenge/`;
  `KIP126/Def.lean` and `KIP126/Challenge.lean` are package entry points.
- [`KIP126.lean`](KIP126.lean) and the modules under [`KIP126/`](KIP126/) are
  authoritative for interfaces and proofs that are actually implemented, as
  well as their import graph.  `Def/` owns mathematical data and properties,
  `External/` owns provenance-bearing inputs, `Challenge/` owns internal proof
  targets, and `Checks/` owns compilation regressions.  The
  [layout migration map](docs/DEF_CHALLENGE_LAYOUT_STATUS.md) records moved
  source modules and remaining open milestones.
- [`reference/source-inventory.json`](reference/source-inventory.json), the
  per-source status records under [`reference/`](reference/), and the Lean
  claim ledger own the catalogue and provenance of external inputs. They record
  evidence and assumptions; they do not turn those inputs into unconditional
  project theorems.

When two sources appear to disagree, resolve the question through the owner
above: scope, trust, and final acceptance through `PROJECT_BOUNDARY.md`;
implemented facts through Lean; planned statements, dependencies, and status
through the Blueprint; long-term order through the Roadmap; and external-input
records through the source inventory and claim ledger.

The intended workflow is therefore:

1. use `aimpaper/` to identify the mathematical target;
2. use `PROJECT_BOUNDARY.md` to decide which claims and inputs are in scope;
3. use `docs/ROADMAP.md` to choose the next implementation slice;
4. record its node-level natural-language statement and Lean correspondence
   in the matching Blueprint chapter; and
5. implement and verify the corresponding Lean declarations with Lake and the
   pinned Mathlib dependency.

The executable Lean implementation is still at the first shared-Core
milestone.  That Core is deliberately small: it imports Mathlib's
`CategoryTheory.SpectralSequence` directly, without a competing wrapper or
synonym, and adds only the category-level filtration data that Mathlib does not
provide: decreasing filtrations of graded objects, associated graded quotients,
filtered morphisms, and filtered chain complexes with their induced
associated-graded differential.  The canonical filtered-complex layer also
constructs homology filtrations, cycle/boundary subobjects, quotient pages, and
finite-page differentials with their square-zero law.  It now also includes the generic
homological-image bridge and the filtered-complex triangulated/abelian
spectral-object adapter; endpoint and convergence data remain explicit
Blueprint interfaces.  The toolchain and Mathlib dependency are pinned to
matching `4.32.2` releases.

The Blueprint remains ahead of the theorem proofs, while the source catalogue
interfaces now cover the completed migration slices.  Its entry
point is [blueprint/src/content.tex](blueprint/src/content.tex), with the
paper-specific chapters under [blueprint/src/chapters](blueprint/src/chapters).
It covers the paper's Sections 1--7, all 401 nonempty appendix rows and nine
zero bands (the rows are now typed AST input records with executable catalogue
regressions), the stable/spectral-sequence/Steenrod/synthetic background absent
from Mathlib, explicit literature and computation provenance, and the full
dependency cone from the compiled Core to the conditional Kervaire endpoints.
All unimplemented nodes are conservatively marked `notready`; the Blueprint
does not claim that the main theorem is already formalized.  Implemented APIs
and planned nodes retain the responsibilities defined once in
`Project documents and workflow` above.

## Build

```sh
lake build
```

The Blueprint PDF, web output, declaration checks, structural doctor, and DAG
checks are maintained separately under `blueprint/` and `.agents/skills/`.

The published Blueprint and API documentation are assembled by
`.github/workflows/pages.yml` and served at
<https://sii-math.github.io/KIP126/>. The workflow prunes work by changed path,
restores only caches written by successful `main` builds, and falls back to a
full component rebuild when a reusable artifact is unavailable. `checkdecls`
is pinned in `lakefile.lean`; the nested `docbuild/` project pins doc-gen4 to
the Lean 4.32.2-compatible commit `1d0643dd819f8ca71b1dd82cba6e3e3050f0a255`.

The Pages workflow uses the following change matrix:

| Changed paths | Blueprint render | Lean/checkdecls | API docs |
| --- | --- | --- | --- |
| `blueprint/src/**` | rebuild | run | reuse artifact |
| `KIP126.lean`, `KIP126/**/*.lean` | reuse artifact | run | rebuild incrementally |
| Lake/toolchain, `docbuild/**`, docs workflow/helpers | rebuild | run | rebuild |
| other paths | workflow skipped | workflow skipped | workflow skipped |

Successful `main` runs are the only writers of the GitHub caches. PRs restore
the trusted Lean baseline and the single doc-gen dependency baseline, but do
not upload `.lake` state. Mathlib files always come from `lake exe cache get`.
The large doc-gen cache has one immutable key per toolchain/manifest graph,
rather than one key per commit. Blueprint and API docs are separate workflow
artifacts; the deploy job assembles them as `_site/blueprint/` and
`_site/docs/`, then uses the Actions Pages artifact flow without a `gh-pages`
branch. A missing component artifact causes a safe rebuild. Weekly and manual
runs skip GitHub caches and record cold plus immediate warm command timings;
normal runs report both elapsed times and cache-hit outcomes in the job summary.
doc-gen equation pages are disabled because the site is used for declaration
types, source links, and search; deriving equations for the full dependency
closure dominates cold builds without improving that evidence chain.

Install the pinned Blueprint renderer, regenerate the declaration list, and
verify that every name resolves in the pinned Lean environment:

```sh
python3 -m pip install --user -r requirements-blueprint.txt
bash scripts/check-blueprint-decls.sh
```

The script regenerates the ignored `blueprint/lean_decls` with
`leanblueprint web` and then runs the pinned `checkdecls` executable configured
in `lakefile.lean`. A removed or renamed Lean declaration is reported by name;
the generated list is not committed.

## Provenance and source inventory

`KIP126.External.Provenance` defines the explicit `SourceId`, `SourceRef`,
`ExternalResult`, and `ExternalEvidence` records.  The typed Lean projection
of the finite catalogue is in `KIP126.External.SourceInventory`, and the
claim-level root/owner/dependency ledger is in `KIP126.External.Claims`.
Citation metadata, acquisition state, artifact paths, and SHA-256 digests are kept in
[`reference/source-inventory.json`](reference/source-inventory.json).  Check
the filesystem ledger and its regression tests with:

```sh
python3 scripts/check_source_inventory.py
python3 -m unittest discover -s scripts -p 'test_check_source_inventory.py'  # unit tests
python3 -m unittest discover -s scripts -p 'test_source_inventory_projection.py'  # Lean integration tests
python3 -m unittest discover -s scripts -p 'test_*.py'  # all tests
lake build KIP126.External.ProvenanceRegression \
  KIP126.External.SourceInventoryRegression \
  KIP126.External.ClaimsRegression
```

On a slow or cold checkout, increase the two Lean subprocess timeouts with
`python3 scripts/check_source_inventory.py --lean-timeout 900`.

The checker validates provenance metadata and reproducibility bookkeeping; it
also rebuilds and executes the Lean exporter, compares all 18 source rows,
checks acquisition-status grammar and canonical artifact kinds, checks all 55
claim rows, and requires every nonempty canonical locator
artifact path to name a listed, `required=true`, existing regular file.  Lean's
`InventoryValid` predicates reject unsafe
paths and paths that fail the syntactic source-directory prefix check, while
`CataloguedExternalResult` and
`CataloguedExternalEvidence` bind an actual wrapper value to one canonical
claim root and compatible trust class; a catalogued evidence artifact must use
the claim locator's canonical path.  The checker compares the checked-in file
with the JSON digest; it does not automatically compare an arbitrary wrapper's
digest field with that value.  None of these checks turns an external record
into an unconditional theorem.  The root, locator, and trust-class
checks are metadata checks: they do not establish that the wrapper proposition
is definitionally the proposition named by a future owner declaration.  The
canonical ledger is closed over 55 explicitly declared, family-level roots;
coverage is relative to that enum rather than a claim that every Blueprint
label has a one-to-one row.

## Repository-private Blueprint skills

The reusable Blueprint workflow lives under
`.agents/skills/` and is intentionally independent of the KIP126 mathematics:

- [leanblueprint-author](.agents/skills/leanblueprint-author/SKILL.md) — write
  source-grounded mathematical chapters;
- [leanblueprint-dag](.agents/skills/leanblueprint-dag/SKILL.md) — inspect and
  repair dependency cones and formalization frontiers;
- [leanblueprint-audit](.agents/skills/leanblueprint-audit/SKILL.md) — audit
  structure, provenance, and Lean/Blueprint drift;
- [leanblueprint-maintain](.agents/skills/leanblueprint-maintain/SKILL.md) —
  build artifacts and safely synchronize proof-status markers.

They complement the global `leanblueprint` environment skill. The maintenance
tools are read-only by default; marker changes require an explicit `--write`.
