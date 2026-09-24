# Project Boundary

## Status

This document records the agreed scope and acceptance criteria for the Lean
formalization of:

> Weinan Lin, Guozhen Wang, and Zhouli Xu, *On the Last Kervaire Invariant
> Problem*, represented in this repository by `aimpaper/main.tex`,
> `aimpaper/112.tex`, and `aimpaper/2412.10879.pdf`.

The document is normative for the project. Any proposed extension or
relaxation of this boundary must be agreed explicitly and recorded here.

## Confirmed design decisions

1. **Homotopy-theoretic foundation.** We use an abstract stable homotopy
   context (option A), not a construction of a complete model of stable
   infinity-categories. The context must expose every operation and property
   needed by the paper's arguments: spectra, maps, homotopy classes,
   suspension, cofibers, distinguished triangles, smash products, homotopy
   groups, and Adams filtrations.

2. **Steenrod algebra and Ext.** We formalize the relevant algebraic
   interfaces and general theorems for the Steenrod algebra, graded objects,
   filtered objects, and Ext/Adams pages. We do not reimplement the large
   high-stem Ext calculations performed by Lin's programs. Concrete
   high-stem values, computer output, and table entries are external inputs
   represented by `ExternalResult` or `ExternalEvidence`.

   For the statement of the permanent `h_6^2` target, the confirmed abstract
   foundation may include an explicit mod--2 Eilenberg--Mac Lane object and
   Milnor cooperation coordinates. These coordinates identify the constructed
   first Adams page with the explicitly defined normalized Milnor cobar
   cochains and intertwine the constructed first differential with the Milnor
   coproduct differential. This structural input is not inferred from the
   homotopy groups of the Eilenberg--Mac Lane object alone. The Adams tower,
   quotient pages, later differentials, page passage, standard `h_6`, its
   concatenation square, and pagewise nonzero permanence must be defined from
   these foundations; they must not be supplied as fields. Proof-route results
   such as C3, C4, and C5 are not part of the statement's defining data. This
   statement-only stage does not establish the conditional final theorem or
   relax the project's proof-completion and axiom-audit acceptance criteria.

   The next agreed stage retains the abstract background and moves the
   comparison foundation below the Adams pages: an associative unital
   structure on the specified `H`, its graded cooperations, and the tensor,
   exactness, and Künneth compatibility needed to construct the comparison.
   The first-page coordinates and their differential compatibility must be
   derived from those foundations. Until that derivation is implemented,
   the existing `MilnorCooperations` argument remains an explicit uneliminated
   dependency; merely renaming or rebundling it does not complete this stage.

3. **Appendix data.** Every entry in the Appendix tables is to be encoded,
   not only the entries used directly in the final proof. The encoding records
   the relevant stem, filtration, class names, differential length, target,
   permanence status, and any stated ambiguity.

4. **Examples, remarks, and questions.**
   - A mathematical assertion in an Example is formalized when it is used by
     a later argument or is needed as a regression test.
   - Expository Remarks are not required to become separate declarations.
   - Open Questions are represented as propositions/statements only; they are
     not assumed and are not required to be proved.

5. **Final geometric conclusions.** Both of the following are conditional
   conclusions:
   - existence of a framed smooth manifold with Kervaire invariant one in
     dimension 126;
   - the assertion that the dimensions are exactly
     `2, 6, 14, 30, 62, 126`.

6. **Axiom policy.** The project may use Lean's foundational axioms and the
   axioms already intrinsic to Lean's standard foundational mechanisms.
   During development, including KIPBase integration, an internal statement
   deliberately introduced with Lean's `axiom` command must be placed in the
   relevant mathematical component's `Axiom.lean`, alongside its `Data.lean`,
   `Predicates.lean`, and `Proofs.lean` where those layers are needed. Each such
   statement must record its source, intended meaning, and reason for being
   assumed, and must be audited individually together with its downstream
   dependencies. Its presence is not evidence that the statement is proved.
   An unfinished theorem instead remains in `Proofs.lean` with `by sorry`;
   it must not be converted into an axiom merely to avoid `sorryAx`.
   Literature results and computational inputs remain explicit external
   premises as specified below, not project axioms. Individual audit makes
   development debt visible; it does not authorize retaining project axioms at
   final acceptance. Every such axiom declaration must be replaced by a proof
   or removed before the final proof-completion criteria below can be met.

7. **Pinned toolchain.**
   - Lean: `4.32.2`
   - mathlib: `v4.32.2`

   The project must use the matching Lean/mathlib versions and must not depend
   on an unpinned `master` branch or a release candidate.

## In-scope formalization

### 1. Algebraic and categorical foundations

The project must formalize the interfaces and required laws for:

- `\mathbb F_2`, graded groups, graded modules, and relevant additive
  structures;
- filtrations and filtered maps;
- chain complexes, homology, exactness, kernels, cokernels, and quotients;
- spectra, maps of spectra, homotopy classes, and homotopy groups;
- suspension and desuspension;
- cofibers, distinguished triangles, and the homotopy category;
- smash products and the naturality/compatibility used in the paper;
- Adams filtration of classes and maps.

The implementation may build on mathlib's category-theory, homological
algebra, homotopy-category, triangulated-category, and spectral-object
infrastructure, while supplying the paper-specific interfaces that mathlib
does not provide.

### 2. Classical Adams spectral sequences

The formalization must include:

- pages, bidegrees, cycles, boundaries, and page-to-page differentials;
- the `E_\infty` page and the relationship to filtered homotopy groups;
- convergence assumptions used by the paper;
- the classical Adams differential convention and degree shifts;
- the elements `h_j`, in particular `h_6^2`;
- the classical extension spectral sequence (ESS);
- essential and inessential extensions;
- crossings, no-crossing conditions, and the associated filtration criteria;
- the propositions and corollaries in Section 2, including naturality and
  composition results.

### 3. `H\mathbb F_2`-synthetic spectra

The abstract synthetic context must include:

- the synthetic category and the functor `\nu`;
- the deformation element `\lambda`;
- synthetic spheres and suspensions;
- `\lambda^n`-quotients;
- the maps `\rho` and `\delta`;
- synthetic Adams spectral sequences;
- the `\lambda`-Bockstein viewpoint;
- rigidity and the comparison interfaces needed by the paper;
- synthetic extension spectral sequences;
- the induced classical `(f, E_r)`-extensions;
- synthetic/classical crossing equivalences.

Foundational theorems imported from earlier papers (for example, the
Pstrągowski and BHS results used to justify these interfaces) are not reproved
here. Their statements are supplied through the external-result mechanism
described below.

### 4. The paper's new results

The following must be proved in Lean from the formalized interfaces and
explicit external inputs:

- Section 2 ESS definitions, propositions, and corollaries;
- synthetic extension results in Sections 3–5;
- the definition and properties of classical `(f, E_r)`-extensions;
- crossing and no-crossing lemmas;
- the Generalized Leibniz Rule;
- the Generalized Mahowald Trick;
- page-stretching and extension-propagation results;
- all logical reductions in Section 7 that do not themselves assert an
  external theorem or a computed table value;
- the conditional permanent-cycle theorem for `h_6^2`.

The proofs must preserve the degree conventions in the paper, including the
third synthetic weight and the translation convention using `S^{1,0}`.

## External inputs

Results from earlier papers, published computations, Lin's program, and facts
read from the Appendix tables are outside the proof-development boundary.
They must not be introduced as Lean `axiom` declarations. Instead, each input
is a value of an explicit structure carrying both the proposition and its
provenance.

The project will use the following conceptual interfaces (the exact field
names may be refined during implementation):

```lean
structure SourceRef where
  source  : SourceId
  locator : Locator
  note    : Option String := none

structure ExternalResult (P : Prop) where
  proof : P
  ref   : SourceRef

structure ArtifactRef where
  path   : String
  sha256 : String
  version : Option String := none

structure ExternalEvidence (P : Prop) where
  evidence : P
  ref      : SourceRef
  method   : String
  artifact : Option ArtifactRef := none
```

`ExternalResult` is intended for a theorem imported from the literature.
`ExternalEvidence` is intended for a computation, program output, table fact, or
other finite evidence record. Both are hypotheses to conditional theorems;
neither is a project-level axiom.

The implementation deliberately separates structural and checkout-facing
validity.  `InventoryValid` adds syntactically safe, source-relative locator
and evidence-artifact paths.  `CataloguedExternalResult` and
`CataloguedExternalEvidence` then bind an actual proposition-bearing wrapper
to one canonical claim root and a compatible trust class.  The Lean claim
ledger proves finite completeness, global source coverage, and acyclicity of
its dependency relation, but remains metadata: it does not prove the recorded
external proposition.  The JSON checker is authoritative for artifact-list
membership of canonical claim locators, required existing-file status, and
SHA-256 equality.  Lean's source-relative condition is syntactic (a directory-prefix
check, not a filesystem/symlink traversal check).  For a dynamically attached
evidence artifact, Lean additionally checks a safe source-relative path and
digest shape; a catalogued wrapper also requires its path to equal the
canonical claim locator.  Lean does not silently assert the file's actual
digest, nor compare an arbitrary wrapper digest automatically.  Root coverage is relative
to the explicitly closed, family-level `ExternalRootId` enum.

Examples of external inputs include:

- Browder's criterion relating Kervaire invariant one manifolds to survival of
  `h_j^2`;
- Barratt--Jones--Mahowald and Burklund--Xu's inductive criterion;
- prior synthetic-spectrum and rigidity theorems;
- May's lemma and other prior-paper results used by the new arguments;
- all concrete Lin-program Ext groups, differentials, extensions, and
  disproofs;
- every entry of the Appendix tables, including entries not used in the final
  proof;
- cited `tmf` detection facts and other prior computational or geometric
  conclusions.

The final proof must make the dependency on these values explicit.

## Conditional final theorems

The project must expose conditional theorems at two levels.

### Homotopy-theoretic conclusion

Under the required external results and evidence, prove that `h_6^2` is a
permanent cycle in the classical Adams spectral sequence.

### Geometric conclusions

Using the external Browder/Pontryagin-type input as an explicit hypothesis,
prove conditionally:

1. there exists a framed smooth manifold with Kervaire invariant one in
   dimension 126;
2. the dimensions in which framed smooth manifolds with Kervaire invariant one
   exist are exactly `2, 6, 14, 30, 62, 126`.

These are implications from explicit `ExternalResult`/`ExternalEvidence` arguments,
not unconditional declarations of the external mathematics.

## Acceptance criteria

The project is complete only when all of the following hold:

- `lake build` succeeds with the pinned Lean/mathlib versions;
- all canonical KIP126 source outside the intentional Challenge statement
  track contains no `sorry` or `admit`, and canonical KIP126 declares no project
  `axiom`; Challenge statements retain their required `by sorry` bodies and
  are excluded from proof-completion evidence, while the isolated historical
  KIPBase component remains subject to its separate migration audit;
- every external input is passed through `ExternalResult` or `ExternalEvidence`;
- every Appendix table entry has a Lean encoding;
- the two geometric conclusions are available as conditional theorems;
- the final theorem(s) pass a `#print axioms` audit with:
  - no `sorryAx`;
  - no project-defined or undeclared custom axiom;
  - Lean foundational axioms allowed by this boundary being the only
    remaining axioms.

The `#print axioms` audit is a hard completion requirement, not merely a
documentation check.

## Explicit non-goals

The project does not attempt to:

- construct a complete model of stable infinity-categories;
- independently reproduce Lin's high-stem computer calculations;
- prove the cited prior-paper theorems;
- treat table values as trusted constants without provenance;
- turn the paper's open Questions into assumptions or claimed results;
- hide external dependencies behind untracked global instances or axioms.
