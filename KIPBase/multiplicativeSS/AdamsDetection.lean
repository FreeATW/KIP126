import KIPBase.multiplicativeSS.AdamsEnriched

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

namespace AdamsDetection

/-- The converging mapping Adams spectral sequence between finite spectra. -/
noncomputable abbrev A (X Y : FiniteSpectra 𝒮) :
    AdamsConvergingSSCategory.{v} :=
  adamsMappingConvergingSS X.1 Y.1 X.2 Y.2

/-- `x ∈ E_r` and `e ∈ E∞` have a common representative in `Z∞`.
The finite-page index is measured from the first Adams page. -/
def HasEInftyClass (X Y : FiniteSpectra 𝒮) (r : ℤ) (k : ℤ × ℤ)
    (x : (A X Y).E.Page r k)
    (e : ((A X Y).E.ssData k).eInfty) : Prop :=
  let D := (A X Y).E.ssData k
  let n : WithTop ℕ := ↑(r - (A X Y).E.r₀).toNat
  ∃ z : (Subobject.underlying.obj (D.Z ⊤) :
      ModuleCat.{v, v} IntModuleRing.{v}),
    (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫
      D.pageπ n) z = x ∧
    D.pageπ ⊤ z = e

/-- A finite-page class is a permanent cycle when it admits a `Z∞`
representative.  Its `E∞` class may still be zero if it is hit by a later
boundary; nonzero survival is a separate condition. -/
def PermanentCycle (X Y : FiniteSpectra 𝒮) (r : ℤ) (k : ℤ × ℤ)
    (x : (A X Y).E.Page r k) : Prop :=
  ∃ e : ((A X Y).E.ssData k).eInfty,
    HasEInftyClass X Y r k x e

/-- An `E∞` class detects an abutment element when that element has a lift
to the filtration prescribed by convergence and the two images in the
associated graded agree.  This is the elementwise form of `Detects`. -/
def EInftyDetects (X Y : FiniteSpectra 𝒮) (k : ℤ × ℤ)
    (e : ((A X Y).E.ssData k).eInfty)
    (α : (A X Y).A ((A X Y).conv.reindex k).2) : Prop :=
  let s := ((A X Y).conv.reindex k).1
  let n := ((A X Y).conv.reindex k).2
  ∃ a : (Subobject.underlying.obj ((A X Y).F.F s n) :
      ModuleCat.{v, v} IntModuleRing.{v}),
    ((A X Y).F.F s n).arrow a = α ∧
    ((A X Y).conv.iso k).hom e =
      ((A X Y).F.toAssociatedGraded s n) a

/-- A finite-page class detects a filtered abutment element through its
`E∞` class.  No independent detection axiom is introduced. -/
def DetectsAbutment (X Y : FiniteSpectra 𝒮) (r : ℤ) (k : ℤ × ℤ)
    (x : (A X Y).E.Page r k)
    (α : (A X Y).A ((A X Y).conv.reindex k).2) : Prop :=
  ∃ e : ((A X Y).E.ssData k).eInfty,
    HasEInftyClass X Y r k x e ∧ EInftyDetects X Y k e α

theorem permanent_of_detects {X Y : FiniteSpectra 𝒮} {r : ℤ} {k : ℤ × ℤ}
    {x : (A X Y).E.Page r k}
    {α : (A X Y).A ((A X Y).conv.reindex k).2}
    (h : DetectsAbutment X Y r k x α) : PermanentCycle X Y r k x := by
  obtain ⟨e, he, _⟩ := h
  exact ⟨e, he⟩

end AdamsDetection

end KIPBase.StableHomotopy
