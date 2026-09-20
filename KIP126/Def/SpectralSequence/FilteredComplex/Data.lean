import KIP126.Def.Algebra.Filtration.Proofs
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# Filtered chain complexes

A filtered chain complex is a Mathlib `ChainComplex` equipped with a decreasing
filtration preserved by the differential.  Unlike the historical KIP core, this
file does not define a second spectral-sequence record or a nested `Z/B`
presentation.  It supplies the associated graded differential needed by a
future construction through Mathlib's spectral-object machinery.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A chain complex together with a decreasing filtration preserved by its
differential. -/
structure FilteredComplex (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The underlying Mathlib chain complex. -/
  complex : ChainComplex C ℤ
  /-- A decreasing filtration of the underlying graded object. -/
  filtration : Algebra.Filtration complex.X
  /-- The differential maps every filtration level into the same level in the
next chain degree. -/
  differential_preserves : ∀ (s k : ℤ),
    ∃ φ : Subobject.underlying.obj (filtration.F s k) ⟶
        Subobject.underlying.obj (filtration.F s (k - 1)),
      φ ≫ (filtration.F s (k - 1)).arrow =
        (filtration.F s k).arrow ≫ complex.d k (k - 1)

namespace FilteredComplex

/-! ### Homology of the underlying complex

The following construction keeps the chain-degree convention explicit.  A
homology object at degree `k` is the homology of the short complex
`X (k + 1) ⟶ X k ⟶ X (k - 1)`. -/

noncomputable def homologyShortComplex (FC : FilteredComplex C) (k : ℤ) :
    ShortComplex C :=
  ShortComplex.mk
    (FC.complex.d (k + 1) k)
    (FC.complex.d k (k - 1))
    (FC.complex.d_comp_d (k + 1) k (k - 1))

/-- The homology graded object of the underlying filtered chain complex. -/
noncomputable def homologyObj (FC : FilteredComplex C) : ℤ → C :=
  fun k => (FC.homologyShortComplex k).homology

@[simp]
lemma homologyObj_apply (FC : FilteredComplex C) (k : ℤ) :
    FC.homologyObj k = (FC.homologyShortComplex k).homology := rfl

/-! ### The induced filtration on homology -/

noncomputable def homologyFiltration (FC : FilteredComplex C) :
    Algebra.Filtration FC.homologyObj where
  F s k :=
    let S := FC.homologyShortComplex k
    let I := kernelSubobject S.g ⊓ FC.filtration.F s k
    let hzero : I.arrow ≫ S.g = 0 := by
      rw [show I.arrow = Subobject.ofLE I (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    imageSubobject (S.liftCycles I.arrow hzero ≫ S.homologyπ)
  decreasing := by
    intro s k
    let S := FC.homologyShortComplex k
    let I₁ := kernelSubobject S.g ⊓ FC.filtration.F (s + 1) k
    let I₀ := kernelSubobject S.g ⊓ FC.filtration.F s k
    have hle : I₁ ≤ I₀ := inf_le_inf_left _ (FC.filtration.decreasing s k)
    have hzero₁ : I₁.arrow ≫ S.g = 0 := by
      rw [show I₁.arrow = Subobject.ofLE I₁ (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have hzero₀ : I₀.arrow ≫ S.g = 0 := by
      rw [show I₀.arrow = Subobject.ofLE I₀ (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have hlift : S.liftCycles I₁.arrow hzero₁ =
        Subobject.ofLE I₁ I₀ hle ≫ S.liftCycles I₀.arrow hzero₀ := by
      apply (cancel_mono S.iCycles).mp
      rw [S.liftCycles_i, Category.assoc, S.liftCycles_i]
      exact (Subobject.ofLE_arrow hle).symm
    have hlift' : S.liftCycles I₁.arrow hzero₁ ≫ S.homologyπ =
        Subobject.ofLE I₁ I₀ hle ≫
          (S.liftCycles I₀.arrow hzero₀ ≫ S.homologyπ) := by
      rw [← Category.assoc, hlift]
    change imageSubobject (S.liftCycles I₁.arrow hzero₁ ≫ S.homologyπ) ≤
      imageSubobject (S.liftCycles I₀.arrow hzero₀ ≫ S.homologyπ)
    rw [hlift']
    exact imageSubobject_comp_le _ _

/-! ### Cycles and boundaries in an associated graded piece -/

/-- The differential from degree `k + 1` to degree `k`.  The canonical chain
complex already indexes its target by `k`, so no degree transport is needed. -/
noncomputable def dToK (FC : FilteredComplex C) (k : ℤ) :
    FC.complex.X (k + 1) ⟶ FC.complex.X k :=
  FC.complex.d (k + 1) k

/-- The `r`-cycle subobject in the associated graded piece. -/
noncomputable def cycleSubobject (FC : FilteredComplex C)
    (s k : ℤ) (r : WithTop ℕ) :
    Subobject (FC.filtration.associatedGraded s k) :=
  let πV := FC.filtration.toAssociatedGraded s k
  match r with
  | ⊤ =>
    let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)
    imageSubobject ((kernelSubobject f).arrow ≫ πV)
  | (n : ℕ) =>
    let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
    imageSubobject ((kernelSubobject f).arrow ≫ πV)

/-- The `r`-boundary subobject in the associated graded piece. -/
noncomputable def boundarySubobject (FC : FilteredComplex C)
    (s k : ℤ) (r : WithTop ℕ) :
    Subobject (FC.filtration.associatedGraded s k) :=
  let πV := FC.filtration.toAssociatedGraded s k
  match r with
  | ⊤ =>
    let imgD := imageSubobject (FC.dToK k)
    let I := imgD ⊓ FC.filtration.F s k
    imageSubobject (Subobject.ofLE I (FC.filtration.F s k) inf_le_right ≫ πV)
  | (n : ℕ) =>
    let imgD := imageSubobject
      ((FC.filtration.F (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k)
    let I := imgD ⊓ FC.filtration.F s k
    imageSubobject (Subobject.ofLE I (FC.filtration.F s k) inf_le_right ≫ πV)

/-- The transported differential squares to zero. -/
theorem dToK_comp_d (FC : FilteredComplex C) (k : ℤ) :
    FC.dToK k ≫ FC.complex.d k (k - 1) = 0 := by
  exact FC.complex.d_comp_d (k + 1) k (k - 1)

/-- Boundaries are cycles in every associated graded piece. -/
theorem B_le_Z_aux (FC : FilteredComplex C) (s k : ℤ)
    (r : WithTop ℕ) :
    FC.boundarySubobject s k r ≤ FC.cycleSubobject s k r := by
  rcases r with _ | n
  · simp only [boundarySubobject, cycleSubobject]
    let ι := Subobject.ofLE (FC.filtration.F (s + 1) k)
      (FC.filtration.F s k) (FC.filtration.decreasing s k)
    let πV := cokernel.π ι
    let imgD := imageSubobject (FC.dToK k)
    let I := imgD ⊓ FC.filtration.F s k
    let oI := Subobject.ofLE I (FC.filtration.F s k) inf_le_right
    let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)
    have h_zero : oI ≫ f = 0 := by
      change Subobject.ofLE I (FC.filtration.F s k) inf_le_right ≫
        (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) = 0
      rw [← Category.assoc, Subobject.ofLE_arrow]
      rw [show I.arrow =
          Subobject.ofLE I imgD inf_le_left ≫ imgD.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm,
        Category.assoc]
      have h : imgD.arrow ≫ FC.complex.d k (k - 1) = 0 := by
        rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
        rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
        exact FC.dToK_comp_d k
      rw [h, comp_zero]
    have heq : oI ≫ πV = factorThruKernelSubobject f oI h_zero ≫
        (kernelSubobject f).arrow ≫ πV := by
      rw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
    calc imageSubobject (oI ≫ πV)
        = imageSubobject (factorThruKernelSubobject f oI h_zero ≫
            (kernelSubobject f).arrow ≫ πV) := by rw [heq]
      _ ≤ imageSubobject ((kernelSubobject f).arrow ≫ πV) :=
          imageSubobject_comp_le _ _
  · simp only [boundarySubobject, cycleSubobject]
    let ι := Subobject.ofLE (FC.filtration.F (s + 1) k)
      (FC.filtration.F s k) (FC.filtration.decreasing s k)
    let πV := cokernel.π ι
    let imgD := imageSubobject
      ((FC.filtration.F (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k)
    let I := imgD ⊓ FC.filtration.F s k
    let oI := Subobject.ofLE I (FC.filtration.F s k) inf_le_right
    let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
    have h_zero : oI ≫ f = 0 := by
      change Subobject.ofLE I (FC.filtration.F s k) inf_le_right ≫
        ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
          cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)) = 0
      simp only [← Category.assoc]
      rw [Subobject.ofLE_arrow]
      rw [show I.arrow =
          Subobject.ofLE I imgD inf_le_left ≫ imgD.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      simp only [Category.assoc]
      have hd : imgD.arrow ≫ FC.complex.d k (k - 1) = 0 := by
        rw [← cancel_epi (factorThruImageSubobject
          ((FC.filtration.F (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k))]
        rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp,
          Category.assoc, FC.dToK_comp_d, comp_zero]
      rw [show imgD.arrow ≫ FC.complex.d k (k - 1) ≫ cokernel.π _ =
        (imgD.arrow ≫ FC.complex.d k (k - 1)) ≫ cokernel.π _
        from (Category.assoc _ _ _).symm,
        hd, zero_comp, comp_zero]
    have heq : oI ≫ πV = factorThruKernelSubobject f oI h_zero ≫
        (kernelSubobject f).arrow ≫ πV := by
      rw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
    calc imageSubobject (oI ≫ πV)
        = imageSubobject (factorThruKernelSubobject f oI h_zero ≫
            (kernelSubobject f).arrow ≫ πV) := by rw [heq]
      _ ≤ imageSubobject ((kernelSubobject f).arrow ≫ πV) :=
          imageSubobject_comp_le _ _

/-- A chain map between filtered complexes which preserves every filtration
level.  The factorisations are kept as explicit data: this is the categorical
version of a filtered chain map and does not identify a filtered subobject with
its ambient object. -/
structure Morphism (FC GD : FilteredComplex C) where
  /-- The underlying Mathlib chain map. -/
  map : FC.complex ⟶ GD.complex
  /-- Factorisations of every component through the target filtration. -/
  preserves : ∀ (s k : ℤ),
    ∃ φ : Subobject.underlying.obj (FC.filtration.F s k) ⟶
        Subobject.underlying.obj (GD.filtration.F s k),
      φ ≫ (GD.filtration.F s k).arrow =
        (FC.filtration.F s k).arrow ≫ map.f k

namespace Morphism

variable {FC GD GE : FilteredComplex C}

@[ext]
lemma ext {f g : Morphism FC GD} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- View a filtered chain map as a filtered morphism of the underlying graded
objects. -/
def toFilteredMorphism (f : Morphism FC GD) :
    Algebra.FilteredMorphism FC.filtration GD.filtration where
  map := fun k => f.map.f k
  preserves := f.preserves

/-- The identity filtered chain map. -/
def id (FC : FilteredComplex C) : Morphism FC FC where
  map := 𝟙 FC.complex
  preserves := fun s k => ⟨𝟙 _, by simp⟩

/-- Composition of filtered chain maps. -/
def comp (f : Morphism FC GD) (g : Morphism GD GE) : Morphism FC GE where
  map := f.map ≫ g.map
  preserves := fun s k => by
    refine ⟨(f.preserves s k).choose ≫ (g.preserves s k).choose, ?_⟩
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [(g.preserves s k).choose_spec, ← Category.assoc,
      (f.preserves s k).choose_spec]
    simp only [Category.assoc]

end Morphism

/-! The filtered complexes and their filtered chain maps form the expected
category.  The proof fields are propositions, so the usual chain-complex
extensionality lemma is enough for the category laws. -/

instance : Category (FilteredComplex C) where
  Hom := Morphism
  id := Morphism.id
  comp f g := Morphism.comp f g
  id_comp f := by
    apply Morphism.ext
    simp [Morphism.comp, Morphism.id]
  comp_id f := by
    apply Morphism.ext
    simp [Morphism.comp, Morphism.id]
  assoc f g h := by
    apply Morphism.ext
    simp [Morphism.comp]

/-- The differential induced on a fixed associated graded piece. -/
noncomputable def associatedGradedDifferential (FC : FilteredComplex C)
    (s k : ℤ) :
    FC.filtration.associatedGraded s k ⟶
      FC.filtration.associatedGraded s (k - 1) := by
  unfold Algebra.Filtration.associatedGraded
  exact cokernel.desc _
    ((FC.differential_preserves s k).choose ≫
      cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) (k - 1))
        (FC.filtration.F s (k - 1)) (FC.filtration.decreasing s (k - 1))))
    (by
      have factor :
          Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k)
              (FC.filtration.decreasing s k) ≫
            (FC.differential_preserves s k).choose =
          (FC.differential_preserves (s + 1) k).choose ≫
            Subobject.ofLE (FC.filtration.F (s + 1) (k - 1))
              (FC.filtration.F s (k - 1)) (FC.filtration.decreasing s (k - 1)) := by
        have mono_arrow : Mono (FC.filtration.F s (k - 1)).arrow := inferInstance
        have lhs_eq :
            (Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k)
                (FC.filtration.decreasing s k) ≫
              (FC.differential_preserves s k).choose) ≫
                (FC.filtration.F s (k - 1)).arrow =
              (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) := by
          rw [Category.assoc, (FC.differential_preserves s k).choose_spec,
            ← Category.assoc, Subobject.ofLE_arrow]
        have rhs_eq :
            ((FC.differential_preserves (s + 1) k).choose ≫
              Subobject.ofLE (FC.filtration.F (s + 1) (k - 1))
                (FC.filtration.F s (k - 1)) (FC.filtration.decreasing s (k - 1))) ≫
                (FC.filtration.F s (k - 1)).arrow =
              (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) := by
          rw [Category.assoc, Subobject.ofLE_arrow,
            (FC.differential_preserves (s + 1) k).choose_spec]
        exact mono_arrow.right_cancellation _ _ (lhs_eq.trans rhs_eq.symm)
      rw [← Category.assoc, factor, Category.assoc, cokernel.condition, comp_zero])

/-- The associated graded differential squares to zero. -/
theorem associatedGradedDifferential_sq (FC : FilteredComplex C)
    (s k : ℤ) :
    FC.associatedGradedDifferential s k ≫
      FC.associatedGradedDifferential s (k - 1) = 0 := by
  unfold associatedGradedDifferential Algebra.Filtration.associatedGraded
  apply (cancel_epi (cokernel.π (Subobject.ofLE
    (FC.filtration.F (s + 1) k) (FC.filtration.F s k)
    (FC.filtration.decreasing s k)))).mp
  simp only [comp_zero, id_eq]
  rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
  suffices h : (FC.differential_preserves s k).choose ≫
      (FC.differential_preserves s (k - 1)).choose = 0 by
    rw [← Category.assoc, h, zero_comp]
  have mono_arrow : Mono (FC.filtration.F s (k - 1 - 1)).arrow := inferInstance
  apply mono_arrow.right_cancellation
  rw [zero_comp, Category.assoc,
    (FC.differential_preserves s (k - 1)).choose_spec,
    ← Category.assoc, (FC.differential_preserves s k).choose_spec,
    Category.assoc, FC.complex.d_comp_d, comp_zero]

/-- The chosen restrictions of the original differential square to zero on
every filtration level. -/
lemma differential_preserves_sq (FC : FilteredComplex C) (s k : ℤ) :
    (FC.differential_preserves s k).choose ≫
        (FC.differential_preserves s (k - 1)).choose = 0 := by
  have mono_arrow : Mono (FC.filtration.F s (k - 1 - 1)).arrow := inferInstance
  apply mono_arrow.right_cancellation
  rw [zero_comp, Category.assoc,
    (FC.differential_preserves s (k - 1)).choose_spec,
    ← Category.assoc, (FC.differential_preserves s k).choose_spec,
    Category.assoc, FC.complex.d_comp_d, comp_zero]

private lemma differential_preserves_sq_transport
    (FC : FilteredComplex C) (s a b c : ℤ)
    (hab : a - 1 = b) (hbc : b - 1 = c) :
    ((FC.differential_preserves s a).choose ≫
        eqToHom (congrArg (fun k =>
          Subobject.underlying.obj (FC.filtration.F s k)) hab)) ≫
      (FC.differential_preserves s b).choose ≫
        eqToHom (congrArg (fun k =>
          Subobject.underlying.obj (FC.filtration.F s k)) hbc) = 0 := by
  subst b
  subst c
  simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
    FC.differential_preserves_sq s a

/-- The chain complex given by one filtration level. -/
noncomputable def filteredChainComplex (FC : FilteredComplex C) (s : ℤ) :
    ChainComplex C ℤ :=
  ChainComplex.of
    (fun k => Subobject.underlying.obj (FC.filtration.F s k))
    (fun k => (FC.differential_preserves s (k + 1)).choose ≫
      eqToHom (congrArg (fun j =>
        Subobject.underlying.obj (FC.filtration.F s j))
        (by omega : (k + 1) - 1 = k)))
    (fun k => by
      apply differential_preserves_sq_transport FC s (k + 1 + 1) (k + 1) k <;>
        omega)

@[simp]
lemma filteredChainComplex_X (FC : FilteredComplex C) (s k : ℤ) :
    (FC.filteredChainComplex s).X k =
      Subobject.underlying.obj (FC.filtration.F s k) := rfl

lemma filteredChainComplex_d (FC : FilteredComplex C) (s k : ℤ) :
    (FC.filteredChainComplex s).d (k + 1) k =
      (FC.differential_preserves s (k + 1)).choose ≫
        eqToHom (congrArg (fun j =>
          Subobject.underlying.obj (FC.filtration.F s j))
          (by omega : (k + 1) - 1 = k)) := by
  dsimp [filteredChainComplex, ChainComplex.of.d]
  simp only [if_true, Category.id_comp]

/-- The canonical inclusion between two filtration levels is a chain map on
the restricted complexes (before the harmless integer-index transports are
inserted by `ChainComplex.of`). -/
lemma filtration_inclusion_comp_differential (FC : FilteredComplex C)
    {t s : ℤ} (h : t ≤ s) (k : ℤ) :
    FC.filtration.inclusion h (k + 1) ≫
        (FC.differential_preserves t (k + 1)).choose =
      (FC.differential_preserves s (k + 1)).choose ≫
        FC.filtration.inclusion h (k + 1 - 1) := by
  apply (cancel_mono (FC.filtration.F t (k + 1 - 1)).arrow).mp
  calc
    (FC.filtration.inclusion h (k + 1) ≫
          (FC.differential_preserves t (k + 1)).choose) ≫
        (FC.filtration.F t (k + 1 - 1)).arrow =
      FC.filtration.inclusion h (k + 1) ≫
        ((FC.differential_preserves t (k + 1)).choose ≫
          (FC.filtration.F t (k + 1 - 1)).arrow) := by
      simp only [Category.assoc]
    _ = FC.filtration.inclusion h (k + 1) ≫
        ((FC.filtration.F t (k + 1)).arrow ≫
          FC.complex.d (k + 1) (k + 1 - 1)) := by
      rw [(FC.differential_preserves t (k + 1)).choose_spec]
    _ = (FC.filtration.F s (k + 1)).arrow ≫
          FC.complex.d (k + 1) (k + 1 - 1) := by
      rw [← Category.assoc, FC.filtration.inclusion_arrow]
    _ = ((FC.differential_preserves s (k + 1)).choose ≫
          (FC.filtration.F s (k + 1 - 1)).arrow) := by
      rw [(FC.differential_preserves s (k + 1)).choose_spec]
    _ = ((FC.differential_preserves s (k + 1)).choose ≫
          FC.filtration.inclusion h (k + 1 - 1)) ≫
          (FC.filtration.F t (k + 1 - 1)).arrow := by
      rw [Category.assoc, FC.filtration.inclusion_arrow]

/-- The inclusion of one filtration level into a lower level, regarded as a
chain map between the restricted complexes.  The target of the map is the
level `t` complex, so the hypothesis is oriented as `t ≤ s`. -/
noncomputable def filtrationInclusionChainMap (FC : FilteredComplex C)
    {t s : ℤ} (h : t ≤ s) :
    FC.filteredChainComplex s ⟶ FC.filteredChainComplex t :=
  ChainComplex.ofHom
    (fun k => FC.filtration.inclusion h k)
    (fun k => by
      dsimp [filteredChainComplex, ChainComplex.of.d]
      simp only [if_true, Category.id_comp]
      -- First use preservation of the ambient differential.  What remains is
      -- just the canonical transport from `(k + 1) - 1` to `k`.
      rw [← Category.assoc, FC.filtration_inclusion_comp_differential h k]
      apply (cancel_mono (FC.filtration.F t k).arrow).mp
      let hk : (k + 1) - 1 = k := by omega
      have ht := FC.filtration.transport_arrow t hk
      have hs := FC.filtration.transport_arrow s hk
      simp only [Category.assoc]
      rw [ht]
      have hinclusion :
          (FC.differential_preserves s (k + 1)).choose ≫
              FC.filtration.inclusion h (k + 1 - 1) ≫
              (FC.filtration.F t (k + 1 - 1)).arrow ≫
              eqToHom (congrArg (fun j : ℤ => FC.complex.X j) hk) =
            (FC.differential_preserves s (k + 1)).choose ≫
              (FC.filtration.F s (k + 1 - 1)).arrow ≫
              eqToHom (congrArg (fun j : ℤ => FC.complex.X j) hk) := by
        simpa only [Category.assoc] using
          congrArg (fun q => (FC.differential_preserves s (k + 1)).choose ≫
            q ≫ eqToHom (congrArg (fun j : ℤ => FC.complex.X j) hk))
            (FC.filtration.inclusion_arrow h (k + 1 - 1))
      have hsource :
          (FC.differential_preserves s (k + 1)).choose ≫
              eqToHom (congrArg (fun j =>
                Subobject.underlying.obj (FC.filtration.F s j)) hk) ≫
              (FC.filtration.F s k).arrow =
            (FC.differential_preserves s (k + 1)).choose ≫
              (FC.filtration.F s (k + 1 - 1)).arrow ≫
              eqToHom (congrArg (fun j : ℤ => FC.complex.X j) hk) := by
        simpa only [Category.assoc] using
          congrArg (fun q => (FC.differential_preserves s (k + 1)).choose ≫ q) hs
      have htarget :
          (FC.differential_preserves s (k + 1)).choose ≫
              eqToHom (congrArg (fun j =>
                Subobject.underlying.obj (FC.filtration.F s j)) hk) ≫
              FC.filtration.inclusion h k ≫
              (FC.filtration.F t k).arrow =
            (FC.differential_preserves s (k + 1)).choose ≫
              (FC.filtration.F s (k + 1 - 1)).arrow ≫
              eqToHom (congrArg (fun j : ℤ => FC.complex.X j) hk) := by
        calc
          (FC.differential_preserves s (k + 1)).choose ≫
                eqToHom (congrArg (fun j =>
                  Subobject.underlying.obj (FC.filtration.F s j)) hk) ≫
                FC.filtration.inclusion h k ≫
                (FC.filtration.F t k).arrow =
              (FC.differential_preserves s (k + 1)).choose ≫
                eqToHom (congrArg (fun j =>
                  Subobject.underlying.obj (FC.filtration.F s j)) hk) ≫
                (FC.filtration.F s k).arrow := by
            simpa only [Category.assoc] using
              congrArg (fun q => (FC.differential_preserves s (k + 1)).choose ≫
                eqToHom (congrArg (fun j =>
                  Subobject.underlying.obj (FC.filtration.F s j)) hk) ≫ q)
                (FC.filtration.inclusion_arrow h k)
          _ = (FC.differential_preserves s (k + 1)).choose ≫
                (FC.filtration.F s (k + 1 - 1)).arrow ≫
                eqToHom (congrArg (fun j : ℤ => FC.complex.X j) hk) := hsource
      rw [hinclusion, htarget])

@[simp]
lemma filtrationInclusionChainMap_f (FC : FilteredComplex C)
    {t s : ℤ} (h : t ≤ s) (k : ℤ) :
    (FC.filtrationInclusionChainMap h).f k = FC.filtration.inclusion h k := rfl

@[simp]
lemma filtrationInclusionChainMap_id (FC : FilteredComplex C) (s : ℤ) :
    FC.filtrationInclusionChainMap (le_rfl : s ≤ s) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact FC.filtration.inclusion_refl s k

@[simp]
lemma filtrationInclusionChainMap_comp (FC : FilteredComplex C)
    {r s t : ℤ} (hrs : r ≤ s) (hst : s ≤ t) :
    FC.filtrationInclusionChainMap hst ≫
        FC.filtrationInclusionChainMap hrs =
      FC.filtrationInclusionChainMap (hrs.trans hst) := by
  apply HomologicalComplex.Hom.ext
  funext k
  change FC.filtration.inclusion hst k ≫ FC.filtration.inclusion hrs k = _
  exact FC.filtration.inclusion_comp hrs hst k

/-- The projective system of restricted chain complexes indexed by the
opposite order on the filtration degree.  An arrow `s ⟶ t` therefore carries
the inclusion from level `s` to the lower level `t`. -/
noncomputable def filteredChainDiagram (FC : FilteredComplex C) :
    (OrderDual ℤ) ⥤ ChainComplex C ℤ where
  obj s := FC.filteredChainComplex s
  map f := FC.filtrationInclusionChainMap f.le
  map_id s := FC.filtrationInclusionChainMap_id s
  map_comp f g := by
    -- In a preorder, the two composite proofs are propositionally equal;
    -- proof irrelevance reduces the index-level inclusions to the lemma above.
    simpa only [Functor.comp_map] using
      (FC.filtrationInclusionChainMap_comp g.le f.le).symm

/-- The cochain-complex presentation of one restricted filtration level.
This uses Mathlib's canonical equivalence between integer-indexed chain and
cochain complexes, so no independent sign convention is introduced here. -/
noncomputable def filteredCochainComplex (FC : FilteredComplex C) (s : ℤ) :
    CochainComplex C ℤ :=
  (ChainComplex.cochainComplexEquivalence C).functor.obj (FC.filteredChainComplex s)

/-- The filtered levels as a cochain-complex diagram.  It is the image of
`filteredChainDiagram` under Mathlib's chain/cochain equivalence. -/
noncomputable def filteredCochainDiagram (FC : FilteredComplex C) :
    (OrderDual ℤ) ⥤ CochainComplex C ℤ :=
  FC.filteredChainDiagram ⋙ (ChainComplex.cochainComplexEquivalence C).functor

@[simp]
lemma filteredCochainDiagram_obj (FC : FilteredComplex C) (s : OrderDual ℤ) :
    (FC.filteredCochainDiagram).obj s = FC.filteredCochainComplex s := rfl

@[simp]
lemma filteredCochainDiagram_map (FC : FilteredComplex C)
    {s t : OrderDual ℤ} (f : s ⟶ t) :
    (FC.filteredCochainDiagram).map f =
      (ChainComplex.cochainComplexEquivalence C).functor.map
        (FC.filtrationInclusionChainMap f.le) := rfl

private lemma associatedGradedDifferential_sq_transport
    (FC : FilteredComplex C) (s a b c : ℤ)
    (hab : a - 1 = b) (hbc : b - 1 = c) :
    (FC.associatedGradedDifferential s a ≫
        eqToHom (congrArg (FC.filtration.associatedGraded s) hab)) ≫
      FC.associatedGradedDifferential s b ≫
        eqToHom (congrArg (FC.filtration.associatedGraded s) hbc) = 0 := by
  subst b
  subst c
  simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
    FC.associatedGradedDifferential_sq s a

/-- The chain complex formed by the associated graded pieces at a fixed
filtration degree. -/
noncomputable def associatedGradedComplex (FC : FilteredComplex C) (s : ℤ) :
    ChainComplex C ℤ :=
  ChainComplex.of
    (fun k => FC.filtration.associatedGraded s k)
    (fun k => FC.associatedGradedDifferential s (k + 1) ≫
      eqToHom (congrArg (FC.filtration.associatedGraded s)
        (by omega : (k + 1) - 1 = k)))
    (fun k => by
      apply associatedGradedDifferential_sq_transport FC s (k + 1 + 1) (k + 1) k <;>
        omega)

@[simp]
lemma associatedGradedComplex_X (FC : FilteredComplex C) (s k : ℤ) :
    (FC.associatedGradedComplex s).X k = FC.filtration.associatedGraded s k := rfl

/-- The displayed consecutive differential of the associated-graded chain
complex is the induced differential, followed by the canonical index
transport. -/
lemma associatedGradedComplex_d (FC : FilteredComplex C) (s k : ℤ) :
    (FC.associatedGradedComplex s).d (k + 1) k =
      FC.associatedGradedDifferential s (k + 1) ≫
        eqToHom (congrArg (FC.filtration.associatedGraded s)
          (by omega : (k + 1) - 1 = k)) := by
  dsimp [associatedGradedComplex, ChainComplex.of.d]
  simp only [if_true, Category.id_comp]

section FilteredMorphismLemmas

variable {FC GD GE : FilteredComplex C}

/-- The quotient projection intertwines the associated-graded differential with
the chosen filtered restriction of the original differential. -/
lemma toAssociatedGraded_comp_associatedGradedDifferential
    (FC : FilteredComplex C) (s k : ℤ) :
    FC.filtration.toAssociatedGraded s k ≫
        FC.associatedGradedDifferential s k =
      (FC.differential_preserves s k).choose ≫
        FC.filtration.toAssociatedGraded s (k - 1) := by
  unfold Algebra.Filtration.toAssociatedGraded associatedGradedDifferential
  exact cokernel.π_desc _ _ _

/-- The filtration-level factorisations of a filtered chain map commute with
the restricted differentials. -/
lemma preserves_differential (f : Morphism FC GD) (s k : ℤ) :
    (f.preserves s k).choose ≫
        (GD.differential_preserves s k).choose =
      (FC.differential_preserves s k).choose ≫
        (f.preserves s (k - 1)).choose := by
  have hF := (f.preserves s k).choose_spec
  have hF' := (f.preserves s (k - 1)).choose_spec
  have hG := (GD.differential_preserves s k).choose_spec
  have hD := (FC.differential_preserves s k).choose_spec
  have hchain := f.map.comm k (k - 1)
  apply (cancel_mono (GD.filtration.F s (k - 1)).arrow).mp
  calc
    ((f.preserves s k).choose ≫
        (GD.differential_preserves s k).choose) ≫
        (GD.filtration.F s (k - 1)).arrow =
      (f.preserves s k).choose ≫
        ((GD.differential_preserves s k).choose ≫
          (GD.filtration.F s (k - 1)).arrow) := by simp only [Category.assoc]
    _ = (f.preserves s k).choose ≫
        ((GD.filtration.F s k).arrow ≫ GD.complex.d k (k - 1)) := by
      rw [hG]
    _ = ((FC.filtration.F s k).arrow ≫ f.map.f k) ≫
        GD.complex.d k (k - 1) := by
      rw [← Category.assoc, hF]
    _ = ((FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
        f.map.f (k - 1) := by
      rw [Category.assoc, hchain, ← Category.assoc]
    _ = ((FC.differential_preserves s k).choose ≫
        (FC.filtration.F s (k - 1)).arrow) ≫ f.map.f (k - 1) := by
      rw [hD]
    _ = (FC.differential_preserves s k).choose ≫
        ((f.preserves s (k - 1)).choose ≫
          (GD.filtration.F s (k - 1)).arrow) := by
      simpa only [Category.assoc] using
        congrArg (fun q => (FC.differential_preserves s k).choose ≫ q) hF'.symm
    _ = ((FC.differential_preserves s k).choose ≫
        (f.preserves s (k - 1)).choose) ≫
        (GD.filtration.F s (k - 1)).arrow := by simp only [Category.assoc]

lemma Morphism.id_preserves_eq (FC : FilteredComplex C) (s k : ℤ) :
    ((Morphism.id FC).preserves s k).choose = 𝟙 _ := by
  apply (cancel_mono (FC.filtration.F s k).arrow).mp
  rw [(Morphism.id FC).preserves s k |>.choose_spec]
  simp [Morphism.id]

lemma Morphism.comp_preserves_eq (f : Morphism FC GD) (g : Morphism GD GE)
    (s k : ℤ) :
    ((Morphism.comp f g).preserves s k).choose =
      (f.preserves s k).choose ≫ (g.preserves s k).choose := by
  apply (cancel_mono (GE.filtration.F s k).arrow).mp
  calc
    ((Morphism.comp f g).preserves s k).choose ≫
          (GE.filtration.F s k).arrow =
        (FC.filtration.F s k).arrow ≫ (Morphism.comp f g).map.f k :=
      (Morphism.comp f g).preserves s k |>.choose_spec
    _ = ((FC.filtration.F s k).arrow ≫ f.map.f k) ≫ g.map.f k := by
      simp only [Morphism.comp, HomologicalComplex.comp_f, Category.assoc]
    _ = ((f.preserves s k).choose ≫ (GD.filtration.F s k).arrow) ≫
          g.map.f k := by rw [(f.preserves s k).choose_spec]
    _ = (f.preserves s k).choose ≫
          ((GD.filtration.F s k).arrow ≫ g.map.f k) := by
      simp only [Category.assoc]
    _ = (f.preserves s k).choose ≫
          ((g.preserves s k).choose ≫ (GE.filtration.F s k).arrow) := by
      rw [(g.preserves s k).choose_spec]
    _ = ((f.preserves s k).choose ≫ (g.preserves s k).choose) ≫
          (GE.filtration.F s k).arrow := by
      simp only [Category.assoc]

private lemma preserves_differential_transport (f : Morphism FC GD)
    (s a b : ℤ) (h : a - 1 = b) :
    (f.preserves s a).choose ≫ (GD.differential_preserves s a).choose ≫
        eqToHom (congrArg (fun k =>
          Subobject.underlying.obj (GD.filtration.F s k)) h) =
      ((FC.differential_preserves s a).choose ≫
        eqToHom (congrArg (fun k =>
          Subobject.underlying.obj (FC.filtration.F s k)) h)) ≫
          (f.preserves s b).choose := by
  subst b
  simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
    preserves_differential f s a

/-- A filtered chain map restricts to a chain map at each fixed filtration
level. -/
noncomputable def Morphism.filteredChainMap (f : Morphism FC GD) (s : ℤ) :
    FC.filteredChainComplex s ⟶ GD.filteredChainComplex s :=
  ChainComplex.ofHom
    (fun k => (f.preserves s k).choose)
    (fun k => by
      dsimp [filteredChainComplex, ChainComplex.of.d]
      simp only [if_true, Category.id_comp]
      apply preserves_differential_transport f s (k + 1) k
      omega)

@[simp]
lemma Morphism.filteredChainMap_f (f : Morphism FC GD) (s k : ℤ) :
    (f.filteredChainMap s).f k = (f.preserves s k).choose := rfl

@[simp]
lemma Morphism.filteredChainMap_id (FC : FilteredComplex C) (s : ℤ) :
    (Morphism.id FC).filteredChainMap s = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact Morphism.id_preserves_eq FC s k

@[simp]
lemma Morphism.filteredChainMap_comp (f : Morphism FC GD)
    (g : Morphism GD GE) (s : ℤ) :
    (Morphism.comp f g).filteredChainMap s =
      f.filteredChainMap s ≫ g.filteredChainMap s := by
  apply HomologicalComplex.Hom.ext
  funext k
  change ((Morphism.comp f g).preserves s k).choose = _
  exact Morphism.comp_preserves_eq f g s k

/-- The restricted complex at a fixed filtration degree is functorial in
filtered chain maps. -/
noncomputable def filteredChainComplexFunctor (s : ℤ) :
    FilteredComplex C ⥤ ChainComplex C ℤ where
  obj FC := FC.filteredChainComplex s
  map f := f.filteredChainMap s
  map_id FC := Morphism.filteredChainMap_id FC s
  map_comp f g := Morphism.filteredChainMap_comp f g s

/-- A filtered chain map gives a natural transformation between the two
filtration-level chain diagrams. -/
noncomputable def Morphism.filteredChainDiagramNatTrans (f : Morphism FC GD) :
    FC.filteredChainDiagram ⟶ GD.filteredChainDiagram where
  app s := f.filteredChainMap s
  naturality {s t} α := by
    apply HomologicalComplex.Hom.ext
    funext k
    change FC.filtration.inclusion α.le k ≫ (f.preserves t k).choose =
      (f.preserves s k).choose ≫ GD.filtration.inclusion α.le k
    apply (cancel_mono (GD.filtration.F t k).arrow).mp
    calc
      (FC.filtration.inclusion α.le k ≫ (f.preserves t k).choose) ≫
            (GD.filtration.F t k).arrow =
          FC.filtration.inclusion α.le k ≫
            ((f.preserves t k).choose ≫ (GD.filtration.F t k).arrow) := by
        simp only [Category.assoc]
      _ = FC.filtration.inclusion α.le k ≫
            ((FC.filtration.F t k).arrow ≫ f.map.f k) := by
        rw [(f.preserves t k).choose_spec]
      _ = (FC.filtration.F s k).arrow ≫ f.map.f k := by
        rw [← Category.assoc, FC.filtration.inclusion_arrow]
      _ = ((f.preserves s k).choose ≫
            (GD.filtration.F s k).arrow) := by
        rw [(f.preserves s k).choose_spec]
      _ = ((f.preserves s k).choose ≫
            GD.filtration.inclusion α.le k) ≫
            (GD.filtration.F t k).arrow := by
        rw [Category.assoc, GD.filtration.inclusion_arrow]

/-- The same natural transformation viewed after the canonical chain/cochain
reindexing. -/
noncomputable def Morphism.filteredCochainDiagramNatTrans (f : Morphism FC GD) :
    FC.filteredCochainDiagram ⟶ GD.filteredCochainDiagram :=
  Functor.whiskerRight f.filteredChainDiagramNatTrans
    (ChainComplex.cochainComplexEquivalence C).functor

/-- The filtration-level diagram construction is itself functorial in filtered
complexes. -/
noncomputable def filteredChainDiagramFunctor :
    FilteredComplex C ⥤ ((OrderDual ℤ) ⥤ ChainComplex C ℤ) where
  obj FC := FC.filteredChainDiagram
  map f := f.filteredChainDiagramNatTrans
  map_id FC := by
    apply NatTrans.ext
    funext s
    exact Morphism.filteredChainMap_id FC s
  map_comp f g := by
    apply NatTrans.ext
    funext s
    exact Morphism.filteredChainMap_comp f g s

/-- The cochain-diagram version of `filteredChainDiagramFunctor`. -/
noncomputable def filteredCochainDiagramFunctor :
    FilteredComplex C ⥤ ((OrderDual ℤ) ⥤ CochainComplex C ℤ) where
  obj FC := FC.filteredCochainDiagram
  map f := f.filteredCochainDiagramNatTrans
  map_id FC := by
    apply NatTrans.ext
    funext s
    change (ChainComplex.cochainComplexEquivalence C).functor.map
      ((Morphism.id FC).filteredChainMap s) = 𝟙 _
    rw [Morphism.filteredChainMap_id]
    simp
  map_comp f g := by
    apply NatTrans.ext
    funext s
    change (ChainComplex.cochainComplexEquivalence C).functor.map
        ((Morphism.comp f g).filteredChainMap s) =
      (ChainComplex.cochainComplexEquivalence C).functor.map
          (f.filteredChainMap s) ≫
        (ChainComplex.cochainComplexEquivalence C).functor.map
          (g.filteredChainMap s)
    rw [Morphism.filteredChainMap_comp]
    simp

/-- The associated-graded map induced by a filtered chain map at one
filtration degree. -/
noncomputable def Morphism.associatedGradedMap (f : Morphism FC GD) (s k : ℤ) :
    FC.filtration.associatedGraded s k ⟶
      GD.filtration.associatedGraded s k :=
  Algebra.FilteredMorphism.associatedGradedMap f.toFilteredMorphism s k

@[simp]
lemma Morphism.associatedGradedMap_id (FC : FilteredComplex C) (s k : ℤ) :
    (Morphism.id FC).associatedGradedMap s k = 𝟙 _ := by
  unfold Morphism.associatedGradedMap Morphism.toFilteredMorphism
  exact Algebra.FilteredMorphism.associatedGradedMap_id _ _ _

@[simp]
lemma Morphism.associatedGradedMap_comp (f : Morphism FC GD)
    (g : Morphism GD GE) (s k : ℤ) :
    (Morphism.comp f g).associatedGradedMap s k =
      f.associatedGradedMap s k ≫ g.associatedGradedMap s k := by
  unfold Morphism.associatedGradedMap Morphism.toFilteredMorphism
  exact Algebra.FilteredMorphism.associatedGradedMap_comp
    f.toFilteredMorphism g.toFilteredMorphism s k

/-- The map induced on associated graded pieces commutes with the induced
differentials. -/
lemma Morphism.associatedGradedMap_comm (f : Morphism FC GD) (s k : ℤ) :
    f.associatedGradedMap s k ≫
        GD.associatedGradedDifferential s k =
      FC.associatedGradedDifferential s k ≫
        f.associatedGradedMap s (k - 1) := by
  unfold Morphism.associatedGradedMap
  apply (cancel_epi (cokernel.π (Subobject.ofLE (FC.filtration.F (s + 1) k)
    (FC.filtration.F s k) (FC.filtration.decreasing s k)))).mp
  have hmap :=
    Algebra.FilteredMorphism.toAssociatedGraded_comp_associatedGradedMap
      f.toFilteredMorphism s k
  have hmap' :=
    Algebra.FilteredMorphism.toAssociatedGraded_comp_associatedGradedMap
      f.toFilteredMorphism s (k - 1)
  have hdiffF :=
    toAssociatedGraded_comp_associatedGradedDifferential FC s k
  have hdiffG :=
    toAssociatedGraded_comp_associatedGradedDifferential GD s k
  have hpreserves := preserves_differential f s k
  calc
    FC.filtration.toAssociatedGraded s k ≫
          f.associatedGradedMap s k ≫
          GD.associatedGradedDifferential s k =
        (f.preserves s k).choose ≫
          GD.filtration.toAssociatedGraded s k ≫
          GD.associatedGradedDifferential s k := by
      simpa only [Category.assoc, Morphism.toFilteredMorphism,
        Morphism.associatedGradedMap] using
        congrArg (fun q => q ≫ GD.associatedGradedDifferential s k) hmap
    _ = (f.preserves s k).choose ≫
          (GD.differential_preserves s k).choose ≫
          GD.filtration.toAssociatedGraded s (k - 1) := by
      simpa only [Category.assoc] using
        congrArg (fun q => (f.preserves s k).choose ≫ q) hdiffG
    _ = (FC.differential_preserves s k).choose ≫
          (f.preserves s (k - 1)).choose ≫
          GD.filtration.toAssociatedGraded s (k - 1) := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ GD.filtration.toAssociatedGraded s (k - 1)) hpreserves
    _ = (FC.differential_preserves s k).choose ≫
          FC.filtration.toAssociatedGraded s (k - 1) ≫
          f.associatedGradedMap s (k - 1) := by
      simpa only [Category.assoc, Morphism.toFilteredMorphism,
        Morphism.associatedGradedMap] using
        congrArg (fun q => (FC.differential_preserves s k).choose ≫ q) hmap'.symm
    _ = FC.filtration.toAssociatedGraded s k ≫
          FC.associatedGradedDifferential s k ≫
          f.associatedGradedMap s (k - 1) := by
      simpa only [Category.assoc, Morphism.associatedGradedMap] using
        congrArg (fun q => q ≫ f.toFilteredMorphism.associatedGradedMap s (k - 1)) hdiffF.symm

private lemma associatedGradedMap_comm_transport (f : Morphism FC GD)
    (s a b : ℤ) (h : a - 1 = b) :
    f.associatedGradedMap s a ≫ GD.associatedGradedDifferential s a ≫
        eqToHom (congrArg (GD.filtration.associatedGraded s) h) =
      (FC.associatedGradedDifferential s a ≫
        eqToHom (congrArg (FC.filtration.associatedGraded s) h)) ≫
          f.associatedGradedMap s b := by
  subst b
  simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
    f.associatedGradedMap_comm s a

/-- The chain map on associated graded complexes induced by a filtered chain
map. -/
noncomputable def Morphism.associatedGradedChainMap (f : Morphism FC GD) (s : ℤ) :
    FC.associatedGradedComplex s ⟶ GD.associatedGradedComplex s :=
  ChainComplex.ofHom
    (fun k => f.associatedGradedMap s k)
    (fun k => by
      dsimp [associatedGradedComplex, ChainComplex.of.d]
      simp only [Category.id_comp]
      apply associatedGradedMap_comm_transport f s (k + 1) k
      omega)

@[simp]
lemma Morphism.associatedGradedChainMap_id (FC : FilteredComplex C) (s : ℤ) :
    (Morphism.id FC).associatedGradedChainMap s = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext k
  change (Morphism.id FC).associatedGradedMap s k = 𝟙 _
  exact Morphism.associatedGradedMap_id FC s k

@[simp]
lemma Morphism.associatedGradedChainMap_comp (f : Morphism FC GD)
    (g : Morphism GD GE) (s : ℤ) :
    (Morphism.comp f g).associatedGradedChainMap s =
      f.associatedGradedChainMap s ≫ g.associatedGradedChainMap s := by
  apply HomologicalComplex.Hom.ext
  funext k
  change (Morphism.comp f g).associatedGradedMap s k =
    f.associatedGradedMap s k ≫ g.associatedGradedMap s k
  exact Morphism.associatedGradedMap_comp f g s k

/-- The fixed-filtration associated-graded construction as a functor. -/
noncomputable def associatedGradedFunctor (s : ℤ) :
    FilteredComplex C ⥤ ChainComplex C ℤ where
  obj FC := FC.associatedGradedComplex s
  map f := f.associatedGradedChainMap s
  map_id FC := Morphism.associatedGradedChainMap_id FC s
  map_comp f g := Morphism.associatedGradedChainMap_comp f g s

end FilteredMorphismLemmas

end FilteredComplex

end KIP126.Core.SpectralSequence
