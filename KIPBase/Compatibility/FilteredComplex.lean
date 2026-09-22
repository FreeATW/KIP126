import KIPBase.SpectralSequence.FilteredComplex
import KIP126.Def.SpectralSequence.Representatives.Proofs

/-!
# Relating the historical filtered-complex API to KIP126

The canonical objects remain KIP126's Mathlib chain complexes. These conversions
allow the historical computations to be checked against that model. Nothing in
KIP126 imports this module. The compiled migration audit requires every declaration
in this namespace to be independent of the historical axioms and `sorryAx`.
-/

namespace KIPBase.Compatibility

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The historical and canonical decreasing filtrations carry the same data. -/
def filtrationEquiv {ι : Type w} (A : ι → C) :
    KIPBase.SpectralSequence.Filtration A ≃ KIP126.Core.Algebra.Filtration A where
  toFun F := ⟨F.F, F.mono⟩
  invFun F := ⟨F.F, F.decreasing⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem filtration_associatedGraded {ι : Type w} {A : ι → C}
    (F : KIPBase.SpectralSequence.Filtration A) (s : ℤ) (k : ι) :
    ((filtrationEquiv A) F).associatedGraded s k = F.associatedGraded s k := rfl

theorem filtration_projection {ι : Type w} {A : ι → C}
    (F : KIPBase.SpectralSequence.Filtration A) (s : ℤ) (k : ι) :
    ((filtrationEquiv A) F).toAssociatedGraded s k = F.toAssociatedGraded s k := rfl

/-- Bounds transport without strengthening the filtration hypotheses. -/
def boundedFiltrationEquiv {ι : Type w} {A : ι → C}
    (F : KIPBase.SpectralSequence.Filtration A) :
    F.IsBounded ≃ ((filtrationEquiv A) F).IsBounded where
  toFun b :=
    { lower := b.lo
      upper := b.hi
      lower_le_upper := b.lo_le_hi
      eq_top_of_le := b.boundedBelow
      eq_bot_of_le := b.boundedAbove }
  invFun b :=
    { lo := b.lower
      hi := b.upper
      lo_le_hi := b.lower_le_upper
      boundedBelow := b.eq_top_of_le
      boundedAbove := b.eq_bot_of_le }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Read a canonical filtered chain complex through the historical API. -/
def toLegacy (FC : KIP126.Core.SpectralSequence.FilteredComplex C) :
    KIPBase.SpectralSequence.FilteredComplex C where
  A := FC.complex.X
  d k := FC.complex.d k (k - 1)
  d_comp_d k := FC.complex.d_comp_d k (k - 1) (k - 1 - 1)
  fil := FC.filtration.F
  fil_anti := FC.filtration.decreasing
  d_preserves_fil := FC.differential_preserves

@[reassoc]
private theorem transport_d (FC : KIPBase.SpectralSequence.FilteredComplex C)
    {i j : ℤ} (h : i = j) :
    eqToHom (congrArg FC.A h) ≫ FC.d j =
      FC.d i ≫ eqToHom (congrArg (fun k => FC.A (k - 1)) h) := by
  subst j
  simp

/-- Construct the Mathlib chain complex underlying historical filtered data.
The transport adjusts the old `k - 1` convention to `ChainComplex.of`'s `k + 1`.
-/
noncomputable def toChainComplex (FC : KIPBase.SpectralSequence.FilteredComplex C) :
    ChainComplex C ℤ :=
  ChainComplex.of FC.A
    (fun k => FC.d (k + 1) ≫ eqToHom (congrArg FC.A (by omega : k + 1 - 1 = k)))
    (fun k => by
      simp only [Category.assoc]
      rw [transport_d_assoc FC (by omega : k + 1 + 1 - 1 = k + 1)]
      simp only [← Category.assoc, FC.d_comp_d, zero_comp])

theorem toChainComplex_d (FC : KIPBase.SpectralSequence.FilteredComplex C) (k : ℤ) :
    (toChainComplex FC).d k (k - 1) = FC.d k := by
  dsimp only [toChainComplex, ChainComplex.of.d]
  rw [dif_pos (by omega)]
  rw [transport_d_assoc FC (by omega : k = k - 1 + 1)]
  simp

/-- Historical constructions can be supplied to the canonical filtered-complex
machinery without assuming equivalence of the two spectral-sequence models. -/
noncomputable def fromLegacy (FC : KIPBase.SpectralSequence.FilteredComplex C) :
    KIP126.Core.SpectralSequence.FilteredComplex C where
  complex := toChainComplex FC
  filtration := ⟨FC.fil, FC.fil_anti⟩
  differential_preserves s k := by
    simpa only [toChainComplex_d] using FC.d_preserves_fil s k

theorem fromLegacy_filtration (FC : KIPBase.SpectralSequence.FilteredComplex C) (s k : ℤ) :
    (fromLegacy FC).filtration.F s k = FC.fil s k := rfl

theorem fromLegacy_differential (FC : KIPBase.SpectralSequence.FilteredComplex C) (k : ℤ) :
    (fromLegacy FC).complex.d k (k - 1) = FC.d k := toChainComplex_d FC k

theorem fromLegacy_associatedGraded (FC : KIPBase.SpectralSequence.FilteredComplex C)
    (s k : ℤ) :
    (fromLegacy FC).filtration.associatedGraded s k = FC.assocGraded s k := rfl

theorem toLegacy_associatedGraded (FC : KIP126.Core.SpectralSequence.FilteredComplex C)
    (s k : ℤ) :
    (toLegacy FC).assocGraded s k = FC.filtration.associatedGraded s k := rfl

theorem toLegacy_projection (FC : KIP126.Core.SpectralSequence.FilteredComplex C)
    (s k : ℤ) :
    (toLegacy FC).filToAssocGraded s k = FC.filtration.toAssociatedGraded s k := rfl

theorem toLegacy_differential (FC : KIP126.Core.SpectralSequence.FilteredComplex C)
    (s k : ℤ) :
    (toLegacy FC).assocGradedDiff s k = FC.associatedGradedDifferential s k := rfl

theorem toLegacy_isLift_iff (FC : KIP126.Core.SpectralSequence.FilteredComplex C)
    {T : C} (s k : ℤ)
    (xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
    (x : T ⟶ FC.filtration.associatedGraded s k) :
    (toLegacy FC).IsLift s k xl x ↔ xl ≫ FC.filtration.toAssociatedGraded s k = x :=
  Iff.rfl

/-- A historical proved result transfers to the canonical differential without
assuming any of the unfinished lift/crossing statements. -/
theorem associatedGradedDifferential_sq_from_legacy
    (FC : KIP126.Core.SpectralSequence.FilteredComplex C) (s k : ℤ) :
    FC.associatedGradedDifferential s k ≫
      FC.associatedGradedDifferential s (k - 1) = 0 :=
  (toLegacy FC).assocGradedDiff_sq s k

end KIPBase.Compatibility
