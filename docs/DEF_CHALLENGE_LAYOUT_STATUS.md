# Def / Challenge migration status

The source paths below describe the current branch. Public Lean declaration names
remain in their original namespaces. The Blueprint chapters and labels remain
the mathematical index; compiling a `Statement.lean` does not prove its node.

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
| `Core/SpectralSequence/FilteredComplex` | `Def/SpectralSequence/FilteredComplex/Data`, `Def/SpectralSequence/FilteredPage/{Data,Proofs,Complex}`, `Def/SpectralSequence/FilteredDifferential/{Data,Proofs}`, `Checks/SpectralSequence/{FilteredComplex,FilteredPage,FilteredDifferential}`, `Challenge/Tools/FilteredComplexRelations/Statement` (canonical filtered complex, homology filtration, cycle/boundary subobjects, page quotient, finite-page differential, and proved `B ≤ Z`/`d² = 0`; Mathlib `SpectralSequence` assembly, full ESS adapter, and four lift/relation obligations remain open) |
| `Core/SpectralSequence/FilteredRepresentatives` | `Def/SpectralSequence/Representatives/Proofs` |
| `Core/SpectralSequence/HomologicalImage` | `Def/SpectralSequence/HomologicalImage/Data` |
| `Core/SpectralSequence/SpectralObjectAdapter` | `Def/SpectralSequence/SpectralObject/Data` |
| `Core/SpectralSequence/Convergence` | `Def/SpectralSequence/EndpointExtension/Data`, `Convergence/{Data,Predicates,Proofs}` |
| `Core/SpectralSequence/Extension` | `Def/SpectralSequence/Extension/Data` (canonical two-term object, differential, chain-complex, square-zero and filtration helpers; full ESS adapter remains open) |
| `SpectralSequence/Crossing` | `Def/PageExtensions/Differential/{Data,Predicates,Proofs}` (partial: finite-page relations; representative equivalence still open) |
| `StableHomotopy/{Basic,TensorTriangulatedCategory}` | `Def/StableHomotopy/Context/{Data,Proofs,MappingProofs}` (category structure, sphere shifts, homotopy-group functor, sphere-smash/mapping-spectrum consequences, distinguished-triangle zero-composition laws, middle-term homotopy-group exactness, and explicit closed/cofiber witness interfaces; connecting-map exactness and model-specific witnesses remain open) |
| `StableHomotopy/Cohomology` | `Def/StableHomotopy/Cohomology/{Data,Proofs}` (explicit HF₂, representable mod-2 cohomology/homology, functorial maps, Steenrod carrier, and universal-coefficient input records; mapping-spectrum action and UCT instances remain supplied data) |
| `Synthetic/{Basic,Sphere}` | `Def/Synthetic/Context/{Data,Proofs}`, `Def/Synthetic/Sphere/Data` (bigraded suspension, λ-powers, λ-cofiber triangles, synthetic spheres, bigraded homotopy, and suspension/λ-action interfaces; enrichment and model-specific equivalences remain open) |
| `Synthetic/Nu` | `Def/Synthetic/Context/{Data,Proofs}` (`NuFunctorData` records the functor, additivity, zero, and suspension witnesses, with derived shift compatibility; cofiber preservation and cohomology-to-homology implications remain open) |
| `Synthetic/Adams` | `Def/Synthetic/AdamsSequence/Data` (Mathlib synthetic page object, λ-page action, grading adapters, and weight-preserving interface; convergence and multiplicative sphere witnesses remain open) |
| `Synthetic/{Lift,Rigidity}` | `Def/Synthetic/Context/Data`, `Def/Comparison/ClassicalSynthetic/{Data,Proofs}`, and the open Challenge/External interfaces (normalized lifts, λ-Bockstein identification, and rigidity are not claimed as proved) |
| `Classical/Adams/Basic` | `Def/StableHomotopy/Context/Data`, `Def/ClassicalAdams/{Page/Data,Convergence/{Data,Predicates,Proofs,StrongData},SphereSequence/Data,H4D2/{Data,Predicates}}`, `External/Literature/Adams/OneLine` |
| `Classical/SpectralSequence/Basic` | `Def/ClassicalAdams/PageSlice/Data` |
| `Classical/ExtensionSS/Basic` | `Def/ClassicalESS/Eta/{Data,ExternalInput,Predicates,Proofs}` |
| `Classical/ExtensionSS/EtaData` | `External/Computation/EtaRows/Data` |
| `Synthetic/SpectralSequence/Basic` | `Def/Synthetic/AdamsSequence/Data` |
| `Comparison/ClassicalSynthetic/Basic` | `Def/Comparison/ClassicalSynthetic/{Data,Proofs}`, `Challenge/Tools/Comparison/{Statement,Proof}` |
| `Classical/Synthetic Kervaire setup` | `Def/Kervaire/Setup/Data`, `Def/Kervaire/Theta5/{Data,Predicates,Proofs}` |
| `External BJM/BX, Xu/IWX, Browder, HHR, BJM inputs` | `External/Literature/Kervaire` |
| `Theorem 6.1 generalized Leibniz` | `Challenge/Tools/Thm6_1Leibniz/Statement` |
| `Theorem 6.12 generalized Mahowald` | `Challenge/Tools/Thm6_12Mahowald/Statement` |
| `Page-extension stretching` | `Challenge/Tools/PagePropagation/Statement` |
| `Theorem 7.3 BJM/BX choice transport` | `Challenge/Near126/Thm7_3BJMBX/Statement`, `Def/Kervaire/Theta5/Proofs` |
| `Candidate differential reduction` | `Challenge/Near126/CandidateReduction/Statement` |
| `C₃/C₄/C₅ choice transport` | `Challenge/Near126/Conditions/Statement` |
| `Final eta-extension exclusion` | `Challenge/Near126/ExcludeEta/Statement` |
| `Proposition 7.8 dichotomy` | `Challenge/Near126/OnlyD12/Statement` |
| `Proposition 7.9 incompatibility` | `Challenge/Near126/C3NotC5/Statement` |
| `Permanent h₆² endpoint` | `Challenge/Final/H6SquarePermanent/Statement` |
| `Dimension-126 geometry` | `Challenge/Geometry/Thm1_1Dimension126/Statement`, `Challenge/Geometry/Cor1_2Dimensions/Statement` |
| `Appendix computation catalogue` | `Def/Computation/AppendixTable/{Data,Rows/{Data,Catalogue}}` |
| `*/Regression`, `*Regression` | corresponding `Checks/` modules |

Import-only facades and empty `Classical/FExtension`, `Classical/PageExtensions`,
`Synthetic/{Adams,ExtensionSS,Rigidity}`, and `Kervaire` placeholders were
removed. `KIPBase/Compatibility/FilteredComplex` now imports the canonical
representatives module; the trusted `KIP126` library still has no `KIPBase`
import. The existing `External/{Provenance,Claims,SourceInventory,Results,Evidence}`
APIs retain their paths.

## Open mathematical obligations

`Challenge/Tools/Comparison/Proof.lean` proves the structural differential
naturality of an existing reindexed chain map. This is a supporting lemma,
not the open `h₄` correspondence or one of the paper's main milestones.

The following paper targets remain `\notready` in the Blueprint and have no
canonical Lean proof: Theorem 6.1 (generalized Leibniz), Theorem 6.12
(generalized Mahowald), Theorem 7.3 (BJM/BX choice transport), Proposition 7.8
(the only-`d₁₂` dichotomy and the C3/C4/C5 equivalence), Proposition 7.9
(C3 excludes C5), Theorem 1.4/7.1 (permanent `h₆²`), Theorem 1.1 (dimension
126), and Corollary 1.2 (exact dimension list). Their precise Lean statements
require the paper-specific stable and synthetic homotopy objects, page
extensions, computation interpretations, and fixed MainInput that are still
Blueprint targets. Each target now has a typed open `Statement.lean`; no
statement is marked as a proof, and no arbitrary witness or external input
asserts an endpoint.

The appendix row schema and all 401 nonempty rows are now encoded as typed AST
records with source locators, 124 joined differential relation pairs, 31
permanent rows, 370 differential rows, and nine explicit zero bands.  The
catalogue has executable length, key uniqueness, metadata, and zero-band
regressions.  It remains an input catalogue: the mathematical interpretation
of each row and its evidence proof are still open.  The existing eta rows are
kept as a separate located computation slice.

`Def/Computation/AppendixTable/Data` gives the twelve paper tables stable
identities, printed table numbers, TeX labels and source line ranges, PDF
pages, spectra, stems, and filtration bands. `Rows/Catalogue` contains the
source-shaped 401-row input and remains `\notready` for theorem completion.

The convergence witness structures now live in `Data`, their detection
relation in `Predicates`, and the derived completion and detection results in
`Proofs`. The provenance-bearing `EtaESSInput` and concrete eta ESS now live
in `ExternalInput`; the eta `Data` file imports only the provenance data type,
not the claim ledger. Public names and statements were preserved.

The canonical filtration layer also now carries the historical
degreewise-Mittag-Leffler predicate and the bounded-above/bounded proofs. This
is a filtration property only; it does not recreate the retired completion
object or its convergence-morphism adapter.

The filtered-complex relation challenge now makes its page adapter explicit:
`PageView` supplies a page-number translation and compares each Mathlib page
with the canonical `pageObj` quotient. A `PageHomologyWitness` supplies a
canonical `PageView` constructor for the finite-page assembly. The new
`PageHomologyFactorization` interface records the exact epi--mono
factorization accepted by Mathlib's homology constructor, and
`PageHomologyWitness.ofFactorization` packages it into the assembly witness;
the inverse `PageHomologyWitness.toFactorization` exposes the same factorization
from any supplied witness.
Its lift predicate factors through the canonical cycle subobject and `pageπ`, and it no
longer identifies every page with the associated graded object. The proved
`PageView.isLift_sub_factors_boundary` lemma records the resulting uniqueness
law: two lifts of one page element differ through the canonical boundary
subobject. The homology witness and the four relation obligations remain
unproved.

The canonical page proof layer also carries the elementary quotient-page laws
formerly provided by `SSData`: bottom boundaries lie in every cycle object, and
a page is zero exactly when its boundary and cycle subobjects coincide. These
are proved directly for `pageObj`; no historical `SSData` structure is copied.
It also owns the nested-subobject quotient maps and third-isomorphism helper
used by the future page-homology comparison.

The canonical filtered-differential proof layer now proves both finite-page
`Z_{n+1} → ker(d_n)` inclusions: the easy direction and the reverse kernel
inclusion `ker(d_n) ≤ image(Z_{n+1} → Z_n → page)`, together with the finite-page
`B_succ` image relation for the next boundary subobject. The proofs also carry
local transport and kernel/image factorization infrastructure for the canonical
`cycleSubobject` API. Each finite quotient page now has a Mathlib
`HomologicalComplex` (`pageComplex`), and an explicit `PageHomologyWitness`
conditionally assembles these pages into Mathlib's `SpectralSequence`. The
concrete factorizations supplying the adjacent-page homology isomorphisms, the
full ESS adapter, and the four lift/relation obligations remain open; no
unconditional `toSpectralSequence` claim is made.

The old `SpectralSequence/Completion` construction is not copied as a second
completion object: KIP126's quotient tower and its eventual-zero limit witness
are the canonical completion interface. The old truncation adapter still
depends on the retired `ConvergenceMorphism`/`PreSS` architecture. Likewise,
`SpectralSequence/UnboundedExtension` and `SpectralSequence/Commutativity`
remain isolated historical evidence because their assembly and convergence
claims depend on that architecture (and the unbounded file contains open
placeholders). No KIP126 theorem claims those constructions were migrated.

Two construction files still import earlier filtration proofs:
`Def/Algebra/Completion/Data` needs the filtration inclusion law to construct
quotient transitions, and `Def/SpectralSequence/FilteredComplex/Data` uses
associated-graded and filtered-morphism results to construct standard
categorical objects. Those constructor-support imports are not yet split into
smaller, earlier data modules.

`Def/PageExtensions/Differential/{Data,Predicates,Proofs}` now owns the Mathlib
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
