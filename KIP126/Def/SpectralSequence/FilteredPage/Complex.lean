import Mathlib.Algebra.Homology.SpectralSequence.Basic
import KIP126.Def.SpectralSequence.FilteredDifferential.Proofs

/-!
# Finite quotient pages as Mathlib homological complexes

The canonical quotient page and its filtered differential determine a Mathlib
`HomologicalComplex` at every finite page.  This is the page-level half of the
future spectral-sequence assembly; the adjacent-page homology isomorphisms are
kept as a separate proof obligation.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The bidegree shape of the finite `n`th page. -/
def pageShape (n : ℕ) : ComplexShape (ℤ × ℤ) :=
  ComplexShape.up' ((n : ℤ), (-1 : ℤ))

set_option maxHeartbeats 800000 in
/-- The differential on a finite quotient page, extended by zero off the page shape. -/
noncomputable def pageDifferentialHom (FC : FilteredComplex C) (n : ℕ)
    (p q : ℤ × ℤ) :
    FC.pageObj p.1 p.2 (n : WithTop ℕ) ⟶ FC.pageObj q.1 q.2 (n : WithTop ℕ) := by
  by_cases hpq : (pageShape n).Rel p q
  · change p + ((n : ℤ), (-1 : ℤ)) = q at hpq
    refine FC.pageDifferential p.1 p.2 n ≫ eqToHom ?_
    rw [← hpq]
    rfl
  · exact 0

set_option maxHeartbeats 800000 in
@[simp]
lemma pageDifferentialHom_of_rel (FC : FilteredComplex C) (n : ℕ)
    (p q : ℤ × ℤ) (hpq : (pageShape n).Rel p q) :
    FC.pageDifferentialHom n p q =
      FC.pageDifferential p.1 p.2 n ≫ eqToHom (by
        rw [← hpq]
        rfl) := by
  dsimp [pageDifferentialHom]
  rw [dif_pos hpq]

set_option maxHeartbeats 800000 in
/-- The finite page as a Mathlib homological complex. -/
noncomputable def pageComplex (FC : FilteredComplex C) (n : ℕ) :
    HomologicalComplex C (pageShape n) where
  X p := FC.pageObj p.1 p.2 (n : WithTop ℕ)
  d p q := FC.pageDifferentialHom n p q
  shape p q hpq := by
    dsimp [pageDifferentialHom]
    rw [dif_neg hpq]
  d_comp_d' p q r hpq hqr := by
    rcases p with ⟨s, k⟩
    rcases q with ⟨s1, k1⟩
    rcases r with ⟨s2, k2⟩
    dsimp [pageDifferentialHom, pageShape, ComplexShape.up'] at hpq hqr ⊢
    rw [dif_pos hpq, dif_pos hqr]
    rcases hpq with ⟨rfl, rfl⟩
    rcases hqr with ⟨rfl, rfl⟩
    convert FC.pageDifferential_comp s k n using 1 <;>
      simp [Int.sub_eq_add_neg]
    all_goals rfl

/-- A finite-page homology comparison is the remaining input for the Mathlib
spectral-sequence assembly. -/
structure PageHomologyWitness (FC : FilteredComplex C) where
  iso : ∀ (n : ℕ) (p : ℤ × ℤ),
    (FC.pageComplex n).homology p ≅
      FC.pageObj p.1 p.2 (↑(n + 1) : WithTop ℕ)

/-- An explicit epi-mono factorization of the page homology map.

The source and target of `π` and `ι` are Mathlib's canonical cycles and
opcycles of `pageComplex`.  Supplying `fac` therefore gives exactly the data
needed by `ShortComplex.HomologyData.ofEpiMonoFactorisation`; the two
factorization maps are required to be epi and mono rather than hidden behind a
second spectral-sequence structure. -/
structure PageHomologyFactorization (FC : FilteredComplex C) where
  π : ∀ (n : ℕ) (p : ℤ × ℤ),
    (FC.pageComplex n).cycles p ⟶
      FC.pageObj p.1 p.2 (↑(n + 1) : WithTop ℕ)
  ι : ∀ (n : ℕ) (p : ℤ × ℤ),
    FC.pageObj p.1 p.2 (↑(n + 1) : WithTop ℕ) ⟶
      (FC.pageComplex n).opcycles p
  fac : ∀ (n : ℕ) (p : ℤ × ℤ),
    (FC.pageComplex n).iCycles p ≫ (FC.pageComplex n).pOpcycles p =
      π n p ≫ ι n p
  π_epi : ∀ (n : ℕ) (p : ℤ × ℤ), Epi (π n p)
  ι_mono : ∀ (n : ℕ) (p : ℤ × ℤ), Mono (ι n p)

namespace PageHomologyFactorization

variable {FC : FilteredComplex C}

/-- The factorization maps identify the supplied page object with page
homology.  This is the canonical Mathlib construction; only the factorization
itself remains to be supplied for a concrete filtered complex. -/
noncomputable def isoHomology (W : PageHomologyFactorization FC)
    (n : ℕ) (p : ℤ × ℤ) :
    FC.pageObj p.1 p.2 (↑(n + 1) : WithTop ℕ) ≅
      (FC.pageComplex n).homology p := by
  let K := FC.pageComplex n
  let kf : KernelFork (K.sc p).g :=
    KernelFork.ofι (K.iCycles p) (K.iCycles_d p _)
  let cc : CokernelCofork (K.sc p).f :=
    CokernelCofork.ofπ (K.pOpcycles p) (K.d_pOpcycles _ p)
  let hkf : IsLimit kf := K.cyclesIsKernel p _ rfl
  let hcc : IsColimit cc := K.opcyclesIsCokernel _ p rfl
  have hEpi : Epi (W.π n p) := W.π_epi n p
  have hMono : Mono (W.ι n p) := W.ι_mono n p
  exact @ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology
    C _ _ (K.sc p) kf cc hkf hcc _ (W.π n p) (W.ι n p)
      (W.fac n p) hEpi hMono

end PageHomologyFactorization

/-- Package a page-homology factorization as the adjacent-page witness used
by the spectral-sequence assembly. -/
noncomputable def PageHomologyWitness.ofFactorization
    (FC : FilteredComplex C) (W : PageHomologyFactorization FC) :
    PageHomologyWitness FC where
  iso n p := (W.isoHomology n p).symm

/-- Recover the epi--mono factorization from an already supplied adjacent-page
homology witness.  This makes the two interfaces definitionally compatible:
the factorization carries no extra mathematical assumption beyond the witness.
-/
noncomputable def PageHomologyWitness.toFactorization
    {FC : FilteredComplex C} (W : PageHomologyWitness FC) :
    PageHomologyFactorization FC where
  π n p := (FC.pageComplex n).homologyπ p ≫ (W.iso n p).hom
  ι n p := (W.iso n p).inv ≫ (FC.pageComplex n).homologyι p
  fac n p := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      (FC.pageComplex n).homology_π_ι p |>.symm
  π_epi n p := epi_comp _ _
  ι_mono n p := mono_comp _ _

/-- Assemble the canonical finite page complexes into Mathlib's spectral
sequence once the adjacent-page homology comparisons are supplied. -/
noncomputable def pageSpectralSequence (FC : FilteredComplex C)
    (W : PageHomologyWitness FC) :
    CategoryTheory.SpectralSequence C (fun r : ℤ => pageShape r.toNat) 0 where
  page r hr := FC.pageComplex r.toNat
  iso r r' p hrr' hr := by
    subst r'
    exact W.iso r.toNat p ≪≫ eqToIso (by
      change FC.pageObj p.1 p.2 (↑(r.toNat + 1) : WithTop ℕ) =
        FC.pageObj p.1 p.2 (↑((r + 1).toNat) : WithTop ℕ)
      congr 2
      omega)

end KIP126.Core.SpectralSequence.FilteredComplex
