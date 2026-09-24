# KIP126 agent guidance

## Agent roles and scope

Agents running in this repository operate in one of two roles:

1. **General-purpose agents** have broad repository access appropriate to their
   assigned task. They are not restricted by the worker-only source boundaries
   below, but remain governed by their task, higher-priority instructions, review
   and merge authorization, and all other repository policies in this file.
2. **Workers** receive one concrete implementation task: either rewrite or complete
   Lean Blueprint source, or implement Lean code. The worker-only contract below
   applies whenever an agent is assigned in that role.

If the task does not explicitly establish that the agent is a worker, do not infer
worker status solely because the task touches Lean or Blueprint files.

## Worker source boundaries

The bound worker skills define the generic authoring, review, and pull-request
workflow. This repository supplies only the mode-specific editable directories:

- Blueprint-only work may edit only files under `blueprint/src/`.
- Lean-only work may edit only `KIP126.lean` and `.lean` files under `KIP126/`.

If a worker task does not select exactly one mode, or requires a path outside the
selected boundary, stop before editing and request that the task be split or
clarified.

## Challenge and Solution synchronization

- Every theorem under `KIP126/Challenge/` must have a corresponding theorem
  under the same relative path in `KIP126/Solution/`, using the respective
  `KIP126.Challenge` and `KIP126.Solution` namespaces.
- Keep their statements synchronized: declaration name, universe parameters,
  variables, typeclass assumptions, explicit and implicit hypotheses, and
  conclusion must agree, apart from the namespace. Update both files in the
  same change whenever a statement changes.
- Challenge declarations are always `theorem ... := by sorry`. Never replace
  them with `def ... : Prop`, fill in their proofs, or remove their statements
  merely because Solution exists.
- Write proofs of these Challenge statements only in Solution. Until a
  solution proof is implemented, its matching theorem also uses `by sorry`;
  an import or explanatory comment alone is not a corresponding Solution theorem.
- Solution proofs must not discharge their goals by invoking the Challenge
  placeholders, directly or indirectly. Import shared definitions and genuine
  proof dependencies instead. Audit Solution and its proof dependencies
  separately from the intentionally unproved Challenge statements; a Challenge
  placeholder is never evidence of proof completion.

## Data, predicates, axioms, and proofs

- Organize each mathematical component under `KIP126/Def/` into separate
  `Data.lean`, `Predicates.lean`, `Axiom.lean`, and `Proofs.lean` modules as
  applicable. Do not mix these responsibilities in one implementation file or
  create empty layers solely to satisfy the naming convention.
- `Data.lean` owns concrete mathematical objects, structures, and operations.
  It must not contain named lemmas/theorems or unfinished property proofs, and
  must not hide `sorry` in data definitions. Required proof fields in a
  construction may use lower-layer property declarations.
- `Predicates.lean` owns the definitions of mathematical conditions and
  relations on those objects. It states predicates, not proofs of them.
- `Axiom.lean`, when needed, owns only statements deliberately introduced with
  Lean's `axiom` command. Keep it beside the other layers of the relevant
  mathematical component, and document each statement's source, intended
  meaning, and reason it is being assumed. These are named project assumptions
  for separate audit, not completed proofs. Do not move an unfinished theorem
  here or turn `by sorry` into an `axiom` to hide proof debt. Literature and
  computation inputs still belong under `KIP126/External/`.
- `Proofs.lean` owns lemmas and theorems about the data and predicates,
  including theorem statements whose proofs temporarily use `by sorry` during
  development. It must not serve as the hidden home of new mathematical data
  definitions or explicit `axiom` declarations.
- Follow the dependency order `Data → Predicates → Axiom → Proofs` where those
  layers are present; a component without axioms may import its predicates
  directly into proofs. Each later module imports only the earlier layers it
  needs. When a further construction needs preservation or well-definedness
  theorems, put it in a subsequent component's `Data.lean` importing the lower
  component's `Proofs.lean`, then separate its predicates and proofs in turn.
  Do not create cyclic imports or
  turn these provable properties into new input hypotheses to avoid the split.
- A public entry module may re-export these layers using imports only.
  Preserve public declaration names when reorganizing files unless the task
  requires an API change.

## Mandatory GitHub synchronization at task start

Before investigating, planning, editing, or validating any task, synchronize the
agent's own checkout with the canonical GitHub repository. The remote default
branch, `origin/main`, is the source of truth; a previously fetched local
`origin/main` ref is not sufficient.

1. Run `git fetch --prune origin`, then inspect `git status` and compare `HEAD`
   and local `main` with `origin/main` (for example with `git rev-list
   --left-right --count ...`).
2. If local `main` is behind and has no local-only commits, fast-forward it with
   `git pull --ff-only origin main` before beginning new code. A feature branch
   must likewise be rebased or merged onto the current `origin/main` before new
   implementation starts, when that is safe and within the task's authorization.
3. If the checkout is dirty, ahead, diverged, cannot fast-forward, or the fetch
   fails, do not reset, overwrite, or silently work from a stale base. Preserve
   the existing work and report the condition or request the needed direction.

This procedure applies only to the agent's task checkout. The persistent
daemon-owned checkout described below remains read-only to agents and must never
be synchronized or otherwise modified by them.

## Readiness and trust boundary

Use the `Project documents and workflow` section of `README.md` as the single map
of which project source answers each kind of question; do not duplicate that map
here. Before editing, base the work on the exact current default-branch head and
check the relevant Blueprint node, its status and dependencies against the actual
Lean declarations and import graph. Also check current issue, pull-request, CI,
and review evidence when they affect readiness. If those sources are missing,
stale, or contradictory, stop and report the conflict instead of guessing.

An unfinished Solution or definition-property proof may temporarily use `sorry`
while it is being developed; the latter remains in its component's `Proofs.lean`.
Challenge proofs remain `sorry` by the rule above. A deliberately introduced
project `axiom` instead belongs in that component's `Axiom.lean` and must be
audited by name and by its downstream dependency cone, separately from
`sorryAx`. Do not mark an unproved or axiom-dependent declaration or its
Blueprint node as complete. A pull request is not mergeable while the required
axiom audit still reports `sorryAx`; this layout policy does not waive any
required check. Before introducing the first canonical `Axiom.lean`, update the
compiled audit and CI to inventory its named axioms separately, reject project
axioms declared elsewhere, and retain the final proof-completion gate.
External hypotheses belong under `KIP126/External/` as provenance-carrying
`ExternalResult` or `ExternalEvidence` inputs, and conclusions that use them
must remain conditional statements taking those inputs explicitly.

## Validation policy

Use the cheapest evidence that answers the task. Do not start with a full build.

1. Inspect the requested change, the relevant diff, and existing validation evidence.
2. For post-merge reviews and read-only questions, check the merged PR checks and the
   successful `main` CI run for the exact merge SHA. If they cover the question, cite
   that evidence and do not repeat `lake build` or `leanblueprint all` locally.
3. Run a focused check only when existing evidence does not answer the question.
4. Deliver changes through a pull request. The required checks for the pull
   request's exact current head are the final mechanical merge gate; local checks
   provide earlier feedback but do not replace or duplicate that gate.

A fresh checkout has no local Lake packages or build outputs. Never run `lake build`
directly in that state: it clones dependencies and then cold-builds them. If local Lean
validation is actually needed, run the narrowest relevant target through the repository's
cache wrapper, for example:

```bash
bash scripts/shared-main-cache.sh run lake build KIP126.SomeModule
```

The wrapper first runs `lake exe cache get` without any project-cache environment, so
Mathlib artifacts still come from Mathlib's official cache. It then overlays KIP126's
latest successful `main` artifact cache from the single daemon's persistent checkout at
`/inspire/hdd/global_user/czxs25250150/KIP126/.lake/shared-main-cache` and executes the
requested command. Do not run `lake update` unless the task is specifically changing
dependency pins.

The persistent checkout `/inspire/hdd/global_user/czxs25250150/KIP126` and everything
under its `.lake/` directory are daemon-owned. Agents must not edit files there, run Git
or Lake write operations there, change permissions, retarget the `current` symlink, or
set that shared path as a writable cache. In particular, never set
`LAKE_ARTIFACT_CACHE=true` while using it and never run `lake cache clean` against it.
Agents may only read it through `scripts/shared-main-cache.sh run`; branch-specific misses
are built in the Agent's own checkout and do not enter the shared cache. If the wrapper
reports no matching cache or a daemon failure, stop and report it instead of modifying the
persistent checkout.

The daemon is the sole writer. It polls `origin/main`, fast-forwards the clean persistent
checkout, skips documentation-only changes using the committed build-input digest, pulls
Mathlib from the official cache, builds changed KIP126 inputs, and atomically publishes a
new immutable generation. Its lifecycle commands are reserved for daemon maintenance:
`bash scripts/shared-main-cache.sh start`, `stop`, and `status`.

GitHub Actions' `kip126-main-build-v2-*` cache contains trusted `.lake/build` output
keyed by OS, architecture, and the committed Lean/build-input digest. Documentation-only
`main` commits therefore reuse their parent's outputs, while Lean source, Lake config or
pins, and toolchain changes get a new key. The repository's workflows restore it
automatically; a Multica local checkout does not. The local wrapper described above uses
the daemon-owned Lake artifact cache instead, not GitHub Actions Cache. Do not claim that
either cache was reused unless the relevant restore actually ran. Prefer exact-SHA CI
results as evidence for read-only analysis.

## Check selection

- Challenge/Solution statement change: compare both complete signatures and
  check both affected modules. Verify that Challenge still uses `by sorry` and
  that Solution does not use the Challenge placeholder as its proof.
- Definition-module reorganization: check the data/predicate/proof separation,
  import direction, and preservation of public declarations, then compile the
  smallest affected downstream target.
- Lean source change: use `scripts/shared-main-cache.sh run` to check the changed module
  or smallest relevant target first. Run a full local `lake build` only when the task
  explicitly requests it or an unresolved question requires it.
- Blueprint prose or graph change: run `leanblueprint web`.
- Changed `\lean` annotations: regenerate the ignored `blueprint/lean_decls` with
  `leanblueprint web`, then run `lake exe checkdecls blueprint/lean_decls`.
- Changed Lean declaration names referenced by the Blueprint: follow the Lean source
  check above, regenerate `blueprint/lean_decls`, and run the same declaration check.
- Print-only Blueprint change: run `leanblueprint pdf`.
- Run `leanblueprint all` only when a task explicitly requires every Blueprint artifact
  or when changes span all of the checks above.
- Non-code/read-only investigation: do not compile solely as a generic preflight.

Before launching an expensive command, state which unresolved question it answers. If
the same commit already has a successful check covering that question, reuse it.
