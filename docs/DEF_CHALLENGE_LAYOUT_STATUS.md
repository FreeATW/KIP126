# Def / Challenge migration status

The source paths below describe the current branch. Public Lean declaration names
remain in their original namespaces. The Blueprint chapters and labels remain
the mathematical index; compiling a `Statement.lean` does not prove its node.

| Former source | Current owner |
| --- | --- |
| `Core/Algebra/Graded`, `Coefficients` | `Def/Algebra/Graded/Data`, `Coefficients/Data` |
| `Core/Algebra/Filtered` | `Def/Algebra/Filtration/{Data,Predicates,Proofs}` |
| `Core/Algebra/Completion` | `Def/Algebra/Completion/{Data,Proofs}` |
| `Core/SpectralSequence/Basic` | `Checks/SpectralSequence/MathlibAPI`; production code imports Mathlib directly |
| `Core/SpectralSequence/PageLevel` | `Def/SpectralSequence/PageLevel/{Data,Proofs}` |
| `Core/SpectralSequence/FilteredComplex` | `Def/SpectralSequence/FilteredComplex/Data` |
| `Core/SpectralSequence/FilteredRepresentatives` | `Def/SpectralSequence/Representatives/Proofs` |
| `Core/SpectralSequence/HomologicalImage` | `Def/SpectralSequence/HomologicalImage/Data` |
| `Core/SpectralSequence/SpectralObjectAdapter` | `Def/SpectralSequence/SpectralObject/Data` |
| `Core/SpectralSequence/Convergence` | `Def/SpectralSequence/EndpointExtension/Data`, `Convergence/{Data,Predicates,Proofs}` |
| `Core/SpectralSequence/Extension` | `Def/SpectralSequence/Extension/Data` |
| `Classical/Adams/Basic` | `Def/StableHomotopy/Context/Data`, `Def/ClassicalAdams/{Page/Data,Convergence/{Data,Predicates,Proofs,StrongData},SphereSequence/Data,H4D2/{Data,Predicates}}`, `External/Literature/Adams/OneLine` |
| `Classical/SpectralSequence/Basic` | `Def/ClassicalAdams/PageSlice/Data` |
| `Classical/ExtensionSS/Basic` | `Def/ClassicalESS/Eta/{Data,ExternalInput,Predicates,Proofs}` |
| `Classical/ExtensionSS/EtaData` | `External/Computation/EtaRows/Data` |
| `Synthetic/SpectralSequence/Basic` | `Def/Synthetic/AdamsSequence/Data` |
| `Comparison/ClassicalSynthetic/Basic` | `Def/Comparison/ClassicalSynthetic/{Data,Proofs}`, `Challenge/Tools/Comparison/{Statement,Proof}` |
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
Blueprint targets. A generic `Prop`, arbitrary witness, or external input
asserting the endpoint would change the mathematical task, so no placeholder
statement or proof is installed for them.

The remaining Appendix row schema and its 401 nonempty rows, the full external literature
interfaces, and the near-126 coherence packages also remain unimplemented.
The existing eta rows are one small, located computation slice; they do not
stand in for the Appendix catalogue.

`Def/Computation/AppendixTable/Data` now gives the twelve paper tables stable
identities, printed table numbers, TeX labels and source line ranges, PDF
pages, spectra, stems, and filtration bands. This is table metadata only;
the row schema, all 401 nonempty rows, and their evidence remain open. Only
the Blueprint definition `def:appendix-table-id` has advanced to `\leanok`.

The convergence witness structures now live in `Data`, their detection
relation in `Predicates`, and the derived completion and detection results in
`Proofs`. The provenance-bearing `EtaESSInput` and concrete eta ESS now live
in `ExternalInput`; the eta `Data` file imports only the provenance data type,
not the claim ledger. Public names and statements were preserved.

Two construction files still import earlier filtration proofs:
`Def/Algebra/Completion/Data` needs the filtration inclusion law to construct
quotient transitions, and `Def/SpectralSequence/FilteredComplex/Data` uses
associated-graded and filtered-morphism results to construct standard
categorical objects. Those constructor-support imports are not yet split into
smaller, earlier data modules.
