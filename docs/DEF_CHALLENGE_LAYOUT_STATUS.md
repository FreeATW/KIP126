# Def / Challenge migration status

The source paths below describe the current branch. Public Lean declaration names
remain in their original namespaces. This is a migration-branch inventory, not
confirmation that the layout is merged or fully compliant with AGENTS.md.
The Blueprint chapters and labels remain
the mathematical index; compiling a Challenge module does not prove its node.

| Former source | Current owner |
| --- | --- |
| `Core/Algebra/Graded`, `Coefficients` | `Def/Algebra/Graded/Data`, `Coefficients/Data` |
| `Core/Algebra/Filtered` | `Def/Algebra/Filtration/{Data,Predicates,Proofs}` |
| `Core/Algebra/Completion` | `Def/Algebra/Completion/{Data,Proofs}` |
| `SpectralSequence/Truncation` | `Def/Algebra/Truncation/{Data,Proofs}` (image filtration and boundedness on canonical quotient objects; no duplicate quotient tower) |
| `Core/SpectralSequence/Basic` | `Checks/SpectralSequence/MathlibAPI`; production code imports Mathlib directly |
| `SpectralSequence/Completion` | `Def/Algebra/Completion/{Data,Proofs}` supplies the canonical quotient tower and explicit completion witnesses; the historical truncation/convergence-morphism adapter is retained only as migration evidence |
| `SpectralSequence/Commutativity` | Retained as isolated historical evidence; its ESS and convergence statements depend on the retired `PreSS`/`ConvergenceMorphism` architecture and are not asserted in KIP126 |
| `SpectralSequence/UnboundedExtension` | Retained as isolated historical evidence; its stabilization and weak-convergence declarations remain open and depend on the retired extension architecture |
| `Core/SpectralSequence/PageLevel` | `Def/SpectralSequence/PageLevel/{Data,Proofs}` |
| `Core/SpectralSequence/FilteredComplex` | `Def/SpectralSequence/FilteredComplex/Data`, `Def/SpectralSequence/FilteredPage/{Data,Proofs,Complex,AssemblyProofs}`, `Def/SpectralSequence/FilteredComplex/Relations/{Data,Predicates,Proofs}`, `Def/SpectralSequence/FilteredDifferential/{Data,Proofs}`, `Checks/SpectralSequence/{FilteredComplex,FilteredPage,FilteredDifferential}`, `Challenge/` only for paper milestones (canonical filtered complex, homology filtration, cycle/boundary subobjects, page quotient, finite-page differential, and proved `B ≤ Z`/`d² = 0`; direct Mathlib `SpectralSequence` assembly is implemented; the full ESS adapter and four lift/relation theorems remain open) |
| `Core/SpectralSequence/FilteredRepresentatives` | `Def/SpectralSequence/Representatives/Proofs` |
| `Core/SpectralSequence/HomologicalImage` | `Def/SpectralSequence/HomologicalImage/Data` |
| `Core/SpectralSequence/SpectralObjectAdapter` | `Def/SpectralSequence/SpectralObject/Data` |
| `Core/SpectralSequence/Convergence` | `Def/SpectralSequence/EndpointExtension/Data`, `Convergence/{Data,Predicates,Proofs}` |
| `Core/SpectralSequence/Extension` | `Def/SpectralSequence/Extension/Data` (canonical two-term object, differential, chain-complex, square-zero and filtration helpers; full ESS adapter remains open) |
| `SpectralSequence/Crossing` | `Def/SpectralSequence/PageDifferential/{Data,Predicates,Proofs}` (partial: finite-page relations; representative equivalence still open) |
| `StableHomotopy/{Basic,TensorTriangulatedCategory}` | `Def/StableHomotopy/Context/{Data,Proofs,MappingProofs}` (category structure, sphere shifts, homotopy-group functor, sphere-smash/mapping-spectrum consequences, distinguished-triangle zero-composition laws, middle-term and connecting-map-at-`Z` homotopy-group exactness, and explicit closed/cofiber witness interfaces; exactness at the shifted `X` term and model-specific witnesses remain open) |
| `StableHomotopy/Cohomology` | `Def/StableHomotopy/Cohomology/{Data,Proofs}` (explicit HF₂, representable mod-2 cohomology/homology, functorial maps, Steenrod carrier, and universal-coefficient input records; mapping-spectrum action and UCT instances remain supplied data) |
| `Synthetic/{Basic,Sphere}` | `Def/Synthetic/Context/{Data,Proofs}`, `Def/Synthetic/Sphere/Data` (bigraded suspension, λ-powers, λ-cofiber triangles, synthetic spheres, bigraded homotopy, and suspension/λ-action interfaces; enrichment and model-specific equivalences remain open) |
| `Synthetic/Nu` | `Def/Synthetic/Context/{Data,Proofs}` (`NuFunctorData` records the functor, additivity, zero, and suspension witnesses, with derived shift compatibility; cofiber preservation and cohomology-to-homology implications remain open) |
| `Synthetic/Adams` | `Def/Synthetic/AdamsSequence/Data` (Mathlib synthetic page object, λ-page action, grading adapters, and weight-preserving interface; convergence and multiplicative sphere witnesses remain open) |
| `Synthetic/{Lift,Rigidity}` | `Def/Synthetic/Context/Data`, `Def/Comparison/ClassicalSynthetic/{Data,Proofs}`, and the open Challenge/External interfaces (normalized lifts, λ-Bockstein identification, and rigidity are not claimed as proved) |
| `Classical/Adams/Basic` | `Def/StableHomotopy/Context/Data`, `Def/ClassicalAdams/{Page/Data,Convergence/{Data,Predicates,Proofs,StrongData},SphereSequence/Data,H4D2/{Data,Predicates}}`, `External/Literature/Adams/OneLine` |
| `Classical/SpectralSequence/Basic` | `Def/ClassicalAdams/PageSlice/Data` |
| `Constructed sphere Adams sequence and standard classes` | `Def/ClassicalAdams/{Tower/Data,TowerPages/{Data,Proofs},TowerDifferential,TowerPageComplex/Data,TowerSequence,Mod2Sphere/Data,MilnorCooperations/{Data,Proofs},SphereClasses/Data}`; differential and page-passage stages each separate data from proofs |
| `Classical/ExtensionSS/Basic` | `Def/ClassicalESS/Eta/{Data,ExternalInput,Predicates,Proofs}` |
| `Classical/ExtensionSS/EtaData` | `External/Computation/EtaRows/Data` |
| `Synthetic/SpectralSequence/Basic` | `Def/Synthetic/AdamsSequence/Data` |
| `Comparison/ClassicalSynthetic/Basic` | `Def/Comparison/ClassicalSynthetic/{Data,Proofs}` |
| `Classical/Synthetic Kervaire setup` | `Def/Kervaire/Setup/Data`, `Def/Kervaire/Theta5/{Data,Predicates,Proofs}` |
| `External BJM/BX, Xu/IWX, Browder, HHR, BJM inputs` | `External/Literature/Kervaire` |
| `Theorem 6.1 generalized Leibniz` | `Challenge/Tools/generalized_leibniz` |
| `Theorem 6.12 generalized Mahowald` | `Challenge/Tools/generalized_mahowald` |
| `Page-extension stretching` | `Challenge/Tools/page_extension_stretch` |
| `Theorem 7.3 BJM/BX choice transport` | `Challenge/Near126/any_choice_criterion`, `Def/Kervaire/Theta5/Proofs` |
| `Candidate differential reduction` | `Challenge/Near126/only_d12_differential_reduction` |
| `C₃/C₄/C₅ choice transport` | `Challenge/Near126/c4_c5_choice_equivalence` |
| `Final eta-extension exclusion` | `Challenge/Near126/c3_excludes_c5` |
| `Proposition 7.8 dichotomy` | `Challenge/Near126/d12_dichotomy_and_condition_equivalence` |
| `Proposition 7.9 incompatibility` | `Challenge/Near126/c3_excludes_c5` |
| `Permanent h₆² endpoint` | `Challenge/Final/h6_sq_permanent` |
| `Dimension-126 geometry` | Blueprint/project-boundary target; its Challenge statements are deferred until the permanent-cycle chain is ready |
| `Appendix computation catalogue` | `External/Computation/AppendixTable/{Data,Proofs,Rows/{Data,Predicates,Catalogue/{Data,Proofs}}}` plus the three unchanged row-chunk modules |
| `*/Regression`, `*Regression` | corresponding `Checks/` modules |

Import-only facades and empty `Classical/FExtension`, `Classical/PageExtensions`,
`Synthetic/{Adams,ExtensionSS,Rigidity}`, and `Kervaire` placeholders were
removed from the canonical tree. The historical
`KIPBase/Compatibility/FilteredComplex` module now directly imports
`Def/SpectralSequence/Representatives/Proofs`; the redundant
`Core/SpectralSequence/FilteredRepresentatives` compatibility entry point has
been removed. The trusted `KIP126` library still has no `KIPBase` import. The existing
`External/{Provenance,Claims,SourceInventory,Results,Evidence}` APIs retain
their paths.

## Open mathematical obligations

The structural differential naturality of the classical/synthetic reindexed
chain map is now a direct theorem in
`Def/Comparison/ClassicalSynthetic/Proofs.lean`. It is a supporting lemma,
not the open `h₄` correspondence or one of the paper's main milestones.

The following paper targets remain `\notready` in the Blueprint and have no
canonical Lean proof: Theorem 6.1 (generalized Leibniz), Theorem 6.12
(generalized Mahowald), Theorem 7.3 (BJM/BX choice transport), Proposition 7.8
(the only-`d₁₂` dichotomy and the C3/C4/C5 equivalence), Proposition 7.9
(C3 excludes C5), Theorem 1.4/7.1 (permanent `h₆²`), Theorem 1.1 (dimension
126), and Corollary 1.2 (exact dimension list). Their precise Lean statements
require the paper-specific stable and synthetic homotopy objects, page
extensions, computation interpretations, and fixed MainInput that are still
Blueprint targets. Each process and permanent-cycle target has a typed open
Challenge module; no statement is marked as a proof, and no arbitrary witness
or external input asserts an endpoint. The two geometric endpoints are
intentionally deferred from `Challenge/` until the permanent-cycle chain is
ready.

The appendix row schema and all 401 nonempty rows are now encoded as typed AST
records with source locators, 124 joined differential relation pairs, 31
permanent rows, 370 differential rows, and nine explicit zero bands.  The
catalogue has executable length, key uniqueness, metadata, and zero-band
regressions.  It remains an input catalogue: the mathematical interpretation
of each row and its evidence proof are still open.  The existing eta rows are
kept as a separate located computation slice.

`External/Computation/AppendixTable/Data` gives the twelve paper tables stable
identities, printed table numbers, TeX labels and source line ranges, PDF
pages, spectra, stems, and filtration bands. `Rows/Catalogue/Data` contains the
source-shaped 401-row input; `Rows/Predicates` defines schema validity and
`Rows/Catalogue/Proofs` checks the transcription. The mathematical interpretation
of the recorded differential and permanence statuses remains `\notready`.
The complete paper-specific schema and catalogue are exported by `KIP126.External`,
not `KIP126.Def`; public names in `KIP126.Computation` are preserved.

The six former loose `ClassicalAdams` implementation files now live in
component directories. Cycle membership is proved before the differential
formula is built; linearity precedes its linear-map construction; boundary
vanishing precedes quotient descent; and the page-passage bijectivity theorem
precedes assembly of the spectral sequence. Each stage separates `Data` and
`Proofs` without introducing artificial predicate layers or additional input
hypotheses. `MilnorCooperations` contains the explicit foundational coordinates
and their cocycle consequence, while `SphereClasses/Data` constructs the standard
classes. Both final Challenge and Solution statements import that same module.

The construction proof chain now proves tower composition, all three
homotopy exactness statements, boundary inclusion in cycles, nesting of
cycles, independence of the differential lift, linearity, vanishing on
boundaries, square-zero, and vanishing of the current differential on
next-page cycles. Polynomial concatenation preserves normalization and
degree and is bilinear; the specified `h6` polynomial and its concatenation
square are closed. `Checks/ClassicalAdams/Construction` audits these completed
lemmas against the foundational axiom allowlist. Eleven of the fourteen
previous foundation `sorry` bodies in the final theorem's local import cone
have been replaced, without adding new placeholders.

This does **not** complete either the comparison or the multiplication task.
The remaining three existing foundation placeholders are
`differentialPolynomial_mem`, `adamsNextBoundaries_le_ker`, and
`adamsNextPageToHomology_bijective`. The general cobar square-zero and Leibniz
proofs, multiplication on its homology, and the actual `E₂` product and square
identity are not yet implemented. The normalized cocycle theorems still
transitively depend on `differentialPolynomial_mem`, although their raw
polynomial counterparts pass the axiom audit.

`StableHomotopy/Cohomology/Multiplication/{Data,Proofs}` adds a monoid-object
structure with unit equal to the specified `H.unit`, the graded groups
`πₙ(H ∧ H)`, unit insertion, and the multiplication counit. It proves that
the Adams unit on `H` splits and that one counit identity holds. It supplies
neither Künneth nor a Milnor identification. `MilnorCooperations` remains an
input to `SphereClasses` and the final theorem, whose proof is still open.

The convergence witness structures now live in `Data`, their detection
relation in `Predicates`, and the derived completion and detection results in
`Proofs`. The provenance-bearing `EtaESSInput` and concrete eta ESS now live
in `ExternalInput`; the eta `Data` file imports only the provenance data type,
not the claim ledger. Public names and statements were preserved.

The canonical filtration layer also now carries the historical
degreewise-Mittag-Leffler predicate and the bounded-above/bounded proofs. This
is a filtration property only; it does not recreate the retired completion
object or its convergence-morphism adapter.

The filtered-complex relation definition layer now makes its page adapter explicit:
`PageView` supplies a page-number translation and compares each Mathlib page
with the canonical `pageObj` quotient. `PageView.canonical` uses the directly constructed
`canonicalPageSpectralSequence`; no separate page-homology witness or
factorization input is required for this construction.
Its lift predicate factors through the canonical cycle subobject and `pageπ`, and it no
longer identifies every page with the associated graded object. The
`Relations/Proofs.lean` module contains the direct theorem declarations: the
uniqueness lemma is proved, while the four relation theorems currently have
`by sorry` proof bodies. They are reusable internal lemmas, not Challenge
milestones. `FilteredPage/AssemblyProofs.lean` constructs `pageHomologyIso`
and `canonicalPageSpectralSequence` directly. See
`SPECTRAL_SEQUENCE_STATUS.md` for the remaining finite-page and convergence work.

The canonical page proof layer also carries the elementary quotient-page laws
formerly provided by `SSData`: bottom boundaries lie in every cycle object, and
a page is zero exactly when its boundary and cycle subobjects coincide. These
are proved directly for `pageObj`; no historical `SSData` structure is copied.
It also owns the nested-subobject quotient maps and third-isomorphism helper
used by the adjacent-page homology comparison.

The canonical filtered-differential proof layer now proves both finite-page
`Z_{n+1} → ker(d_n)` inclusions: the easy direction and the reverse kernel
inclusion `ker(d_n) ≤ image(Z_{n+1} → Z_n → page)`, together with the finite-page
`B_succ` image relation for the next boundary subobject. The proofs also carry
local transport and kernel/image factorization infrastructure for the canonical
`cycleSubobject` API. Each finite quotient page now has a Mathlib
`HomologicalComplex` (`pageComplex`). The kernel/image calculations give
`pageHomologyIso`, and `canonicalPageSpectralSequence` assembles these pages
into Mathlib's `SpectralSequence` without a separate homology-witness input.
This finite-page construction does not settle convergence, the full ESS
adapter, or the four lift/relation obligations.

The old `SpectralSequence/Completion` construction is not copied as a second
completion object: KIP126's quotient tower and its eventual-zero limit witness
are the canonical completion interface. The old truncation adapter still
depends on the retired `ConvergenceMorphism`/`PreSS` architecture. Likewise,
`SpectralSequence/UnboundedExtension` and `SpectralSequence/Commutativity`
remain isolated historical evidence because their assembly and convergence
claims depend on that architecture (and the unbounded file contains open
placeholders). No KIP126 theorem claims those constructions were migrated.

## Remaining layout work

Importing an earlier component's proofs from a later construction's Data
module is permitted by AGENTS.md. Such an import alone is not a layout defect.
The outstanding defects are declarations with the wrong layer ownership:

- Data modules still contain named proofs, including
  `Def/Algebra/Filtration/Data` and `Def/SpectralSequence/FilteredComplex/Data`.
- Proof modules still construct mathematical objects, including
  `homotopyGroupFunctor` in `Def/StableHomotopy/Context/Proofs` and
  `canonicalPageSpectralSequence` in
  `Def/SpectralSequence/FilteredPage/AssemblyProofs`.

Move construction-support laws into earlier proof components and the resulting
objects into subsequent Data components, preserving public names and acyclic
imports. Top-level relocation does not make these files compliant.

## Remaining mathematical and historical boundaries

`Def/SpectralSequence/PageDifferential/{Data,Predicates,Proofs}` now owns the Mathlib
page-level
differential, essentiality, crossing, and no-crossing interfaces inspired by
the historical crossing definitions. Essentiality means the target class is
nonzero; the original relation may be zero. This does not prove equivalence
with the historical ambient representative or complete target-coset model. This is foundation data for the paper's
page-extension nodes; the finite/infinite synthetic page-extension statements
and their crossing equivalences remain open in the Blueprint.

The truncation port deliberately covers the quotient image filtration and its
boundedness laws. The historical convergence-morphism truncation adapter and
the universal `IsComplete` predicate still belong to the existing completion
and convergence interfaces; they are not claimed as migrated by this slice.

The stable/synthetic context port now exposes explicit category, bigraded
suspension, fully-faithful suspension, λ-power cofiber, synthetic-sphere, and
ν-functor witness interfaces. It does not assert the historical global
synthetic cofiber, enrichment, ν-cofiber preservation, λ-Bockstein, rigidity,
or normalized-lift axioms; those remain explicit model inputs or open internal
proof obligations.

The preservation checker for the isolated historical component is currently
blocked by source drift on `origin/main`: the immutable
`migration/kip-base/source-4.28.tar.gz` snapshot predates later `KIPBase`
changes in the bounded-extension and commutativity files, so
`scripts/kipbase-migration.py` stops at its trust-debt comparison.  The archive
and ledger are left unchanged; refreshing that archival baseline is a separate
repository-maintenance decision.
