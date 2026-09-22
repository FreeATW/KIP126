# Def / Challenge / Solution layout specification

Status: layout contract for the migration branch; implementation is incomplete.
This does not claim that the migration has landed on main or passed acceptance.
The original proposal's branch name and frozen base are historical Git metadata,
not a requirement to work from an old checkout.

Use README.md's **Project documents and workflow** section to locate the
authoritative mathematical, scope, implementation, and provenance sources.
AGENTS.md supplies the repository's source rules and validation procedure.
This document describes the layout contract; DEF_CHALLENGE_LAYOUT_STATUS.md
records current ownership and remaining migration work.

## Data, predicates, and proofs

Organize each component under KIP126/Def/ into the layers it actually needs:

| File | Responsibility | Dependencies |
| --- | --- | --- |
| Data.lean | Objects, structures, maps, operations, and constructions | Mathlib and earlier components, including their proved construction laws |
| Predicates.lean | Definitions of conditions and relations | Relevant data layers; not its own proof layer |
| Proofs.lean | Lemmas and theorems about data and predicates | Data, predicates where needed, and earlier proofs |

Data files contain no named lemmas/theorems or hidden sorry in data definitions.
Required structure fields may use lower-layer property results. Predicate files
state conditions rather than prove them. Proof files must not become the home
of new mathematical objects or constructions. An unfinished property theorem
may temporarily use `by sorry`, but is not completed evidence.
Do not create empty layers simply to match the table.

When a construction requires a preservation or well-definedness theorem,
prove it in the earlier component's Proofs.lean, then put the construction in
a subsequent component's Data.lean. Continue the split for its predicates and
proofs. Do not create cycles or replace a provable law with a new input
hypothesis to avoid this separation.

Public entry modules re-export components with imports only. Preserve public
declaration names unless the task requires an API change. A reusable implication
is a direct theorem, not a parallel `def statement : Prop` alias.
Paper milestones belong to Challenge/Solution; supporting lemmas belong to Def.

## Challenge / Solution contract

KIP126/Challenge/ and KIP126/Solution/ have matching relative paths and entry
modules. Theorems have the same names, universe parameters, variables,
typeclass assumptions, hypotheses, and conclusions, modulo the respective
KIP126.Challenge and KIP126.Solution namespace prefixes. Public structures
and fields must also remain synchronized where mirrored.

Challenge theorems always have `:= by sorry`; they remain statement
placeholders even after the Solution proof is complete. Write proofs only in
Solution. An unfinished Solution theorem also uses `by sorry`; an import or
comment does not satisfy the mirror requirement. Solution must not use
Challenge placeholders, directly or indirectly.

Additions, removals, renames, and statement changes update both tracks in the
same change. Proof-only Solution changes do not require Challenge edits.
Compare relative trees and complete signatures during validation.
Compiling a placeholder is never proof-completion evidence and must not
justify a Blueprint completion marker.

## Source ownership

Paths are relative to KIP126/ and describe the current migration tree.
They do not require empty directories for planned mathematics.

| Area | Current owner |
| --- | --- |
| Algebra | Def/Algebra/ |
| Filtered complexes, quotient pages, finite-page assembly, convergence interfaces | Def/SpectralSequence/ |
| Generic page differential, essentiality, crossing, and no-crossing predicates | Def/SpectralSequence/PageDifferential/ |
| Stable homotopy and cohomology | Def/StableHomotopy/ |
| Classical Adams constructions and sphere classes | Def/ClassicalAdams/ |
| Synthetic contexts, spheres, and Adams data | Def/Synthetic/ |
| Classical eta ESS interfaces | Def/ClassicalESS/Eta/ |
| Classical/synthetic comparison | Def/Comparison/ |
| Kervaire setup, sphere Adams interface, theta-five choices | Def/Kervaire/ |
| Literature inputs | External/Literature/ |
| Paper-specific appendix schema, encoded rows, computation inputs | External/Computation/ |
| Source and claim bookkeeping | External/Provenance.lean, External/SourceInventory.lean, External/Claims.lean |
| Milestone statements and proofs | Challenge/, Solution/ |
| Compilation and statement-shape regressions | Checks/ |

The appendix schema and catalogue are exported by KIP126.External, not
KIP126.Def; public names in KIP126.Computation are preserved. Encoded rows and
metadata checks do not establish mathematical truth.

Synthetic ESS, full paper-specific page extensions, and geometric endpoints
remain planned mathematics where no implementation exists. The generic
page-differential API is not a completed synthetic page-extension model.

## Current milestone modules

Paths below are relative to both Challenge/ and Solution/. The Blueprint
remains the mathematical statement and dependency index; this table is a
module locator, not a proof-completion claim.

| Target | Relative module |
| --- | --- |
| Generalized Leibniz rule | Tools/generalized_leibniz.lean |
| Generalized Mahowald trick | Tools/generalized_mahowald.lean |
| Page-extension stretching | Tools/page_extension_stretch.lean |
| BJM/BX choice transport | Near126/any_choice_criterion.lean |
| Candidate differential reduction | Near126/only_d12_differential_reduction.lean |
| Exclusive dichotomy and three-condition equivalence | Near126/d12_dichotomy_and_condition_equivalence.lean |
| C4/C5 choice transport | Near126/c4_c5_choice_equivalence.lean |
| C3/C5 incompatibility and final exclusion | Near126/c3_excludes_c5.lean |
| Permanent h6-square endpoint | Final/h6_sq_permanent.lean |

The sourced BJM/BX input belongs to External/Literature/Kervaire.lean;
its project-level choice transport remains a separate proof obligation.
Geometry statements are deferred until the permanent-cycle chain is ready,
without removing those targets from the project boundary.

## Import and trust boundaries

- Keep imports acyclic. Def must not import Challenge; Solution and its proof
  dependencies must not rely on Challenge placeholders.
- Production mathematics must not import Checks. Canonical KIP126 modules
  must not import KIPBase. Historical reuse requires a port with checked
  statements and recursive axiom dependencies.
- External facts enter as explicit, provenance-bearing ExternalResult or
  ExternalEvidence inputs about the same objects used by their consumers.
  Do not add project axioms or move internal proof obligations into External.
- Imports express compilation dependencies; Blueprint dependency edges
  express mathematical dependencies. They need not be identical.
- Audit Solution and its actual dependencies separately from intentional
  Challenge placeholders. Completion requires no sorryAx or project-defined
  axiom in the claimed proof. The current recursive audit and CI behavior do
  not establish that this separation is already enforced.

## Remaining migration and acceptance

Top-level relocation does not finish migration. Complete the outstanding
Data/Predicates/Proofs separation recorded in the status document, preserve
public APIs, and synchronize module locators and README commands.
Do not waive a source rule because an existing file still violates it.

Use the focused checks required by AGENTS.md. For documentation-only path
corrections, inspect source existence and the diff; do not run Lean or
Blueprint builds as a generic preflight. Lean or Blueprint source changes
require their corresponding checks. Exact-head PR checks remain the mechanical
merge gate; this document does not waive failures. Mathematical completion
and merge readiness are separate from directory migration.

Deliver changes through pull requests. This document neither changes the
project's mathematical scope nor certifies unproved declarations or nodes.
