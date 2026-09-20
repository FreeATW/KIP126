import KIP126.Def.SpectralSequence.Convergence.Data
import KIP126.Def.SpectralSequence.FilteredPage.Complex
import KIP126.Def.StableHomotopy.Context.Proofs

/-!
# Open statements from the historical KIP-base library

The historical stable-homotopy and spectral-sequence files contain several
declarations whose bodies are `sorry`.  Their mathematical targets can still
be recorded against the canonical KIP126 objects.  This file contains only
those target propositions: it does not import `KIPBase`, add an axiom, or
declare a theorem with an unfinished proof.

The first statement is the remaining exactness assertion in the long exact
sequence of a chosen cofiber triangle.  The other two statements expose the
finite-page and convergence obligations that are represented by explicit
KIP126 witness structures.  A concrete proof must construct the witnesses or
prove the requested property; merely having a `PageHomologyWitness` or a
`PageAbutmentComparisonWitness` is not treated as a completed theorem.
-/

namespace KIP126.Challenge.Tools.StableHomotopy

open CategoryTheory
open KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FilteredComplex
open KIP126.StableHomotopy

universe u v

/-! ### Stable-homotopy exactness -/

/-!
The shifted map out of `X` is the map that follows the connecting
homomorphism in the long exact sequence.  This is the direct canonical form
of the historical `les_homotopy_exact_h` target.
-/
def lesHomotopyExactH : Prop :=
  ∀ {C : Type u} [StableHomotopyCategory.{u, v} C]
    (T : HoCofiberSequence (C := C)) (n : ℤ),
    ∀ (x : HomotopyGroup (n - 1) T.X),
      (inducedMap T.f (n - 1)) x = 0 ↔
        ∃ z : HomotopyGroup n T.Z, (connectingHomomorphism T n) z = x

/-! ### Finite-page comparison -/

/-!
The canonical finite-page complexes are already available in
`FilteredPage.Complex`.  The remaining assembly input is the adjacent-page
homology comparison, represented by `PageHomologyWitness`.
-/
def pageHomologyWitnessExists : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    (FC : FilteredComplex C), Nonempty (PageHomologyWitness FC)

/-! ### Strong convergence -/

/-!
This is the convergence target after a pointwise page/abutment comparison has
been supplied.  The comparison witness carries the explicit boundedness and
endpoint data; the conclusion asks for the coherent stable-page and
`E∞` identifications in `StrongConvergenceWitness`.
-/
def strongConvergenceFromComparison : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    (FC : FilteredComplex C) (P : EndpointExtension FC)
    (A : Type u) [Category.{v} A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological]
    (W : PageAbutmentComparisonWitness P A F),
    ∃ S : StrongConvergenceWitness P A F, S.comparison = W

end KIP126.Challenge.Tools.StableHomotopy
