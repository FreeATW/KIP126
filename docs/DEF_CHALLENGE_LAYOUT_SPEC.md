# Def / Challenge layout specification

Status: proposed implementation specification. Branch: `feat/def-challenge-layout`.
Base: `origin/main` at `d6ec1ce8a6b2d6f9a5f011ba1212415b307baa5e` (2026-09-18).

This document specifies a source layout for the KIP126 formalization. It does not
change the mathematical scope or mark any Blueprint node complete. The target
paper in `aimpaper/`, the acceptance boundary in `PROJECT_BOUNDARY.md`, the
Blueprint statements and dependencies, and the implemented Lean declarations
retain the responsibilities assigned by `README.md`.

## Goals and non-negotiable boundaries

1. Make each important mathematical object and proof obligation a discoverable
   Lean module. Direct `import` edges expose compilation dependencies. Blueprint
   `\uses` continues to record the finer mathematical dependency graph; the two
   graphs need not have identical edges.
2. Separate candidate data, independently stated properties, and proofs. A
   definition carries only the data and laws required to construct its type.
   Properties such as locality, convergence, vanishing, comparison isomorphisms,
   and detection are named propositions with separate proofs.
3. Put only paper-level milestone statements in `Challenge/`. Concrete object
   properties belong in `Def/*/Predicates.lean`; reusable internal deductions
   belong in `Def/*/Proofs.lean`. Both kinds of theorem are written directly as
   `theorem` declarations; during development an unfinished proof body may be
   `by sorry`. A compiling declaration is not a proof-completion marker.
4. Keep literature results and finite computational facts as explicit,
   provenance-carrying `ExternalResult` or `ExternalEvidence` parameters. The
   final permanent-cycle theorem remains conditional on these inputs and has
   no project-defined axiom or `sorryAx` dependency. The Lean foundational
   allowlist remains the one in `scripts/Axioms.lean`.
5. Keep `KIPBase` isolated. Its compatibility module is migration evidence,
   not an import path into the trusted `KIP126` library. A reusable historical
   declaration enters `Def/` only after its statement, model, and recursive
   axiom dependencies have been checked and its proof ported.

## Three-layer declaration rule

This is the source-level rule for the migration discussed in this document.
It is deliberately stricter than merely splitting files by topic.

1. **Data / definitions.** `Def/*/Data.lean` defines the mathematical objects,
   maps, operations, and witness records. A structure may contain the laws
   required to construct that object. It must not hide an unproved theorem in
   an arbitrary field merely to make later code typecheck.
2. **Predicates.** `Def/*/Predicates.lean` defines reusable properties and
   relations of those objects as `Prop`. Examples are `IsLift`,
   `DifferentialRelation`, and `RelationCrossedBy`. A predicate describes an
   object or configuration; it is not itself a paper milestone.
3. **Proofs.** `Def/*/Proofs.lean` states reusable mathematical results as
   direct `theorem` declarations. The theorem type is the statement, and its
   proof body is written immediately after `:=`; while a proof is being
   developed that body may be `by sorry`. There is no parallel
   `def statement : Prop` or `def conclusion : Prop` for the same result.

The same direct-theorem rule applies to `Challenge/*/Statement.lean`, but a
Challenge file is reserved for an important paper milestone. A supporting
lemma that is useful because of the formalization, rather than because it is a
milestone of the paper, belongs in `Def/*/Proofs.lean`. A milestone theorem may
take the formalized definitions, predicates, and explicit external inputs as
premises. Its temporary `by sorry` body records an unfinished proof; it does
not make the theorem trusted or complete, and it must not receive a Blueprint
completion marker.

For migration decisions, use this test:

```text
Is it an object or witness?                 -> Def/*/Data.lean
Is it a reusable property or relation?      -> Def/*/Predicates.lean
Is it a reusable mathematical implication?  -> Def/*/Proofs.lean theorem
Is it a paper-level milestone?              -> Challenge/*/Statement.lean theorem
```

The file split is not a requirement to rename public declarations. Existing
names may be retained when that avoids unnecessary downstream churn; what must
change is the ownership and the absence of a separate proposition alias for a
theorem statement.

## Challenge / Solution mirror contract

`KIP126/Solution/` is a parallel proof track for the current Challenge graph.
It must have the same relative directories and Lean files as
`KIP126/Challenge/`, including a matching `KIP126/Solution.lean` entrypoint.
The mirrored files use the `KIP126.Solution` namespace and import other
Solution nodes rather than importing `Challenge/`; this keeps the two tracks
independent for a later comparator.

For every mirrored node, the public statement is the same: declaration names,
namespaces modulo the `Challenge`/`Solution` prefix, parameters, typeclass
arguments, structure fields, and theorem types must agree. A Solution proof
may replace the Challenge file's temporary `by sorry` body, but it must not
silently change the statement while the comparator is being used.

The two trees are synchronized in the same change. Adding, deleting, or
renaming a Challenge node requires the corresponding operation in
`Solution/`; changing a Challenge mathematical object, structure field, or
theorem statement requires the matching Solution statement to be updated at
the same time. Proof-body-only changes in Solution do not require a Challenge
change. Validation must include a tree/statement comparison before a change is
considered ready for the future comparator.

## Target source tree

All new Lean modules stay below `KIP126/`. Lake's recursive library glob, the
canonical axiom audit, and the CI path filters already use that root. Names in
the tree are ownership boundaries, not a requirement to create empty files.

```text
KIP126/
  Def/
    Algebra/                 Graded, Filtration, Completion, Coefficients
    SpectralSequence/        FilteredComplex, PageLevel, Representatives,
                             HomologicalImage, SpectralObject, Convergence
    StableHomotopy/          context, spectra, maps, cofibers, smash, filtration
    ClassicalAdams/          pages, bidegrees, h_j, sphere sequence
    Synthetic/               synthetic context, nu, lambda, spheres, Adams
    ClassicalESS/            ESS, f-extensions
    SyntheticESS/            synthetic extensions
    PageExtensions/          extension, crossing, no-crossing interfaces
    Comparison/              classical/synthetic comparison data and predicates
    Computation/             table schemas and interpretation types
    KervaireSetup/           fixed contexts, coherence, near-126 conditions
  External/
    Literature/             BHS/Pstragowski, BJM/BX, Browder, HHR, etc.
    Computation/            Lin outputs, appendix rows, finite spectra/maps,
                             stems 122/125/126 and other finite evidence
    Provenance.lean         existing source-reference API
    Claims.lean             existing claim-ledger API
    SourceInventory.lean    existing finite source catalogue
  Challenge/
    Tools/                  comparison, generalized rules, page propagation
    Near126/                candidate reduction through final exclusion
    Final/                  conditional h6-square permanent-cycle theorem
  Solution/                 one-to-one proof-track mirror of `Challenge/`
  Checks/                   focused regression and statement-shape modules
```

Each leaf concept under `Def/<area>/<concept>/` normally has:

| File | Owns | Import constraint |
| --- | --- | --- |
| `Data.lean` | One principal object, map, operation, or candidate construction and its type-required laws | Imports only earlier data and Mathlib as needed |
| `Predicates.lean` | Separately named `Prop` definitions about that data | Imports `Data`, not its proofs |
| `Proofs.lean` | Proved properties and conversion theorems | Imports `Predicates` and needed earlier proofs |

A helper stays with its principal declaration when it has no independent
consumer. An independently reusable declaration gets its own leaf concept.
For a `Functor`, `ChainComplex`, or similar standard type whose constructor
requires laws, first expose the raw data and named law when that improves
review, prove the law, and then assemble the standard object. No arbitrary
choice from an unproved existence statement may stand in for the specified
object.

Each `Challenge/<node>/` normally has a `Statement.lean` containing the exact
paper milestone as a direct theorem declaration, with all required parameters
and explicit external conditions. An open theorem may use the temporary body
`by sorry`; there is no separate `def statement : Prop`. Reusable supporting
theorems are kept in the corresponding `Def/*/Proofs.lean` module rather than
in `Challenge/`.

## Correspondence with KIP126 dependency diagram 1

The diagram's boxes map to subtrees. A box may contain several Lean nodes;
arrows become specific imports and explicit theorem arguments. The Blueprint
chapter and label remain the mathematical index.

| Diagram box or region | Owning source area | Blueprint chapter or anchor |
| --- | --- | --- |
| Algebraic foundations | `Def/Algebra/` | `algebraic_foundations.tex` |
| Spectral-sequence machinery | `Def/SpectralSequence/` | `spectral_sequences.tex` |
| Stable homotopy context | `Def/StableHomotopy/` | `stable_homotopy.tex` |
| Classical Adams and HF2-synthetic homotopy | `Def/ClassicalAdams/`, `Def/Synthetic/` | `classical_adams.tex`, `synthetic_homotopy.tex` |
| Classical and synthetic ESS | `Def/ClassicalESS/`, `Def/SyntheticESS/` | `extension_spectral_sequences.tex`, `synthetic_extensions.tex` |
| Page extensions, crossing, no-crossing | `Def/PageExtensions/` | `page_extensions.tex` |
| Kervaire setup and conditions C3/C4/C5 | `Def/KervaireSetup/` | `kervaire_setup.tex`, `near126.tex` |
| Classical/synthetic comparison interface and proof | `Def/Comparison/` | `comparison_and_rules.tex` |
| Generalized Leibniz and Mahowald | `Challenge/Tools/Thm6_1Leibniz/`, `Challenge/Tools/Thm6_12Mahowald/` | `thm:generalized-leibniz`, `thm:generalized-mahowald` |
| Page stretching and extension propagation | `Challenge/Tools/PagePropagation/` | `comparison_and_rules.tex` |
| Candidate reduction | `Challenge/Near126/CandidateReduction/` | `near126.tex` |
| Only the possible nonzero d12 remains | `Challenge/Near126/OnlyD12/` | `prop:possible-h62` |
| Relations among C3/C4/C5 | `Challenge/Near126/Conditions/` | `near126.tex` |
| C3 implies not C5 | `Challenge/Near126/C3NotC5/` | `prop:near126-c3-not-c5` |
| Exclude the final eta-extension scenario | `Challenge/Near126/ExcludeEta/` | `near126.tex` |
| Conditional permanent-cycle endpoint | `Challenge/Final/H6SquarePermanent/` | `thm:h6-square-permanent` |
| Synthetic rigidity / lambda-Bockstein / Pstragowski / BHS | `External/Literature/Synthetic/` | `external_results.tex` |
| BJM/BX source criterion | `External/Literature/BJMBX/` | `thm:external-bjm-bx-criterion` |
| Lin programs, appendix rows, finite spectra/maps, stem evidence | `External/Computation/` | `computed_inputs.tex` |

The BJM/BX source theorem and the paper's project deduction have distinct
owners. `External/Literature/BJMBX/` contains the sourced criterion for its
specified choice. `Challenge/Near126/Thm7_3BJMBX/` proves the required
transport to the paper's choice using the explicit external input and the
choice-independence result. The latter corresponds to Blueprint label
`thm:bjm-bx-criterion-any-choice`.

The appendix schema belongs to `Def/Computation/`; the 401 nonempty rows and
their finite evidence belong to `External/Computation/` and the existing
`reference/` inventory. A row's encoded data and its asserted mathematical
truth remain distinguishable.

## Challenge index

The eight Prove2me milestone titles are planning inputs. Their current
platform Lean statements are not automatically accepted as KIP126 statements.
The paper and Blueprint determine each final type; the platform record keeps
the cross-reference. The permanent-cycle main theorem is an additional node.

| Paper target | Challenge node | Blueprint anchor |
| --- | --- | --- |
| Theorem 6.1, Generalized Leibniz Rule | `Tools/Thm6_1Leibniz` | `thm:generalized-leibniz` |
| Theorem 6.12, Generalized Mahowald Trick | `Tools/Thm6_12Mahowald` | `thm:generalized-mahowald` |
| Theorem 7.3, BJM/BX criterion for required choices | `Near126/Thm7_3BJMBX` | `thm:bjm-bx-criterion-any-choice` |
| Proposition 7.8, exclusive dichotomy | `Near126/OnlyD12` | `prop:possible-h62` |
| Proposition 7.8, three-condition equivalence | `Near126/Conditions` | `prop:possible-h62` and its supporting nodes |
| Proposition 7.9, C3/C5 incompatibility | `Near126/C3NotC5` | `prop:near126-c3-not-c5` |
| Theorem 1.4 / 7.1, permanent h6-square | `Final/H6SquarePermanent` | `thm:h6-square-permanent` |

The geometric endpoints follow the permanent-cycle theorem and the separately
supplied Browder, low-dimensional, and HHR results. They remain in the
Blueprint and `PROJECT_BOUNDARY.md`, but their typed Challenge nodes are
deferred until the permanent-cycle chain is ready.

## Import and trust rules

```text
Mathlib -> Def/*/Data -> Def/*/Predicates -> Def/*/Proofs
                  \-> External input types and records
Def + External -> Challenge/*/Statement and Solution/*/Statement
                   (paper milestones; temporary `sorry` is allowed)
Challenge/Tools -> Challenge/Near126 -> Challenge/Final
```

1. `Def/` never imports `Challenge/`. Challenge statements import only the
   declarations needed to type their goal; their proof files import earlier
   proof nodes. `Checks/` may import any canonical module but is not imported
   by mathematical production modules.
2. Imports expose compilation dependencies, possibly including declarations
   unused by one theorem. Blueprint `\uses` records logical dependencies and
   must be checked against the theorem's actual constants and hypotheses.
3. An external result has a proposition about the *same* chosen contexts,
   maps, classes, and degree conventions used by its consumer. It enters as
   an explicit parameter, never as a global theorem, instance, or axiom.
4. Internal results required by the paper, including the generalized rules,
   Near-126 reduction, and permanent-cycle theorem, remain proof obligations.
   Moving them into `External/` is not a route to completion.
5. `KIPBase` has no import edge into `KIP126`. Its 94 historical axioms and
   source placeholders do not enter the canonical final theorem's dependency
   cone. Reuse proceeds declaration by declaration with a trusted proof.
6. `Challenge/` and `Solution/` are synchronized statement tracks. A
   comparator may reject a change when their relative trees or public theorem
   statements diverge.

## Migration sequence

1. **Inventory and freeze.** Record the exact `origin/main` SHA, current
   declaration names, import graph, Blueprint `\lean` and `\uses` links, and
   the current Challenge targets above and their Solution mirrors. Classify
   each current declaration as data, predicate, proof, external-input
   machinery, or regression check.
2. **Representative vertical slice.** Split one existing filtration concept
   under `Def/Algebra/Filtration/` and add one compiling Challenge statement.
   Preserve the public declaration names where possible. Verify that Lake,
   the axiom audit, and Blueprint declaration checking still see the files.
3. **Move foundations in dependency order.** Migrate `Core/Algebra`, then
   `Core/SpectralSequence`, then stable, classical, synthetic, ESS, page
   extension, comparison, and Kervaire setup declarations. Keep temporary
   import-only facades where needed; remove them after consumers move.
4. **Add the paper milestone graph.** Create the `Tools`, `Near126`, `Final`,
   and `Geometry` theorem declarations in the order above. Keep reusable
   object-level predicates and supporting theorem declarations under `Def/`.
   Do not mark a node `leanok` because its theorem compiles with `sorry`.
5. **Reconcile the project map.** Update the `README.md` and `docs/ROADMAP.md`
   chapter-to-module wording from an intended one-file mapping to a chapter
   entry point over multiple small modules. Keep the Blueprint chapters in
   their present mathematical order; update `\lean` names only when a public
   declaration is intentionally renamed.

Each slice is independently reviewable. A refactor-only slice preserves
mathematical statements and the recursive axiom dependencies of moved
declarations. Any discovered statement correction is reviewed as a separate
mathematical change, with the relevant Blueprint node updated.

## Acceptance criteria for the layout migration

- Every new Lean source is under `KIP126/`, appears in the Lake library, and is
  included in `scripts/Axioms.lean`'s recursive audit.
- The proposed import direction is acyclic. No canonical module imports
  `KIPBase`; no `Def` module imports `Challenge`.
- Open Challenge statements may compile with an explicit `sorry` theorem body
  and contain no project-defined axiom or arbitrary data standing in for the
  specified object. Before merge, the reusable `Def/*/Proofs.lean` theorem
  bodies required by a milestone must be checked for `sorry`, `admit`, and
  project axioms. Only actual proofs cause Blueprint completion markers to
  advance.
- Existing public declarations retain their names or have reviewed import,
  Blueprint, and downstream-reference updates. The proof and assumption
  meaning of each moved declaration is unchanged.
- `Solution/` mirrors the current Challenge tree and statement types. Any
  Challenge statement change has a matching Solution update in the same
  change; a Solution proof body may become stronger without changing that
  mirrored type.
- External inputs remain explicit and catalogued; the main theorem cannot
  obtain its own conclusion from an input field.
- Focused module builds pass during migration. For the final structural PR,
  the exact-head CI, canonical axiom audit, Blueprint web/declaration checks,
  and relevant regression checks pass. A full local build is run only when a
  concrete unresolved question requires it; CI is the final merge gate.

This specification itself changes documentation only. Implementation and
verification evidence will be attached to subsequent changes on this branch
and delivered through the repository's pull-request workflow.
