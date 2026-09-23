import KIP126.Def.SpectralSequence.Basic.Data
import KIP126.Def.Algebra.Filtration.Data

/-!
# Convergence data for nested-subobject spectral sequences

This file migrates the data declarations from
`KIPBase/SpectralSequence/Convergence.lean`.  The historical field names are
preserved.  Explicit conversions connect its filtration record to the existing
`KIP126.Core.Algebra.Filtration` API.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A decreasing filtration with the historical `mono` field name. -/
structure Filtration {ω : Type w} (A : ω → C) where
  /-- Filtration subobject at level `s` and grading `k`. -/
  F : ℤ → (k : ω) → Subobject (A k)
  /-- Successive levels form a decreasing family. -/
  mono : ∀ (s : ℤ) (k : ω), F (s + 1) k ≤ F s k

/-- Convert the spectral-sequence filtration API to KIP126's algebra filtration API. -/
def Filtration.toAlgebra {ω : Type w} {A : ω → C} (F : Filtration A) :
    KIP126.Core.Algebra.Filtration A where
  F := F.F
  decreasing := F.mono

/-- Convert KIP126's algebra filtration API to the spectral-sequence API. -/
def _root_.KIP126.Core.Algebra.Filtration.toSpectralSequence
    {ω : Type w} {A : ω → C} (F : KIP126.Core.Algebra.Filtration A) :
    Filtration A where
  F := F.F
  mono := F.decreasing

/-- Associated graded piece `F^s A^k / F^(s+1) A^k`. -/
noncomputable def Filtration.associatedGraded
    {ω : Type w} {A : ω → C} (F : Filtration A) (s : ℤ) (k : ω) : C :=
  cokernel (Subobject.ofLE (F.F (s + 1) k) (F.F s k) (F.mono s k))

/-- Projection from a filtration level to its associated graded piece. -/
noncomputable def Filtration.toAssociatedGraded
    {ω : Type w} {A : ω → C} (F : Filtration A) (s : ℤ) (k : ω) :
    Subobject.underlying.obj (F.F s k) ⟶ F.associatedGraded s k :=
  cokernel.π (Subobject.ofLE (F.F (s + 1) k) (F.F s k) (F.mono s k))

/-- Transport associated graded pieces along equality of their indices. -/
noncomputable def Filtration.transportGraded
    {ω' : Type w} {A : ω' → C} (F : Filtration A)
    {r₁ r₂ : ℤ × ω'} (h : r₁ = r₂) :
    F.associatedGraded r₁.1 r₁.2 ⟶ F.associatedGraded r₂.1 r₂.2 :=
  eqToHom (by rw [h])

/-- Weak convergence to a filtered graded object. -/
structure Convergence
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    (E : SpectralSequence C ω) {ω' : Type w} (A : ω' → C) (F : Filtration A) where
  /-- Reindexing from spectral-sequence degrees to filtration/stem degrees. -/
  reindex : ω → ℤ × ω'
  /-- The reindexing is bijective. -/
  reindex_bijective : Function.Bijective reindex
  /-- Identification of the infinity page with the associated graded. -/
  iso : ∀ (k : ω),
    (E.ssData k).eInfty ≅ F.associatedGraded (reindex k).1 (reindex k).2

/-- Filtration-degree component of the convergence reindexing. -/
def Convergence.filtrationDegree
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ℤ :=
  (conv.reindex k).1

/-- Stem-degree component of the convergence reindexing. -/
def Convergence.stemDegree
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ω' :=
  (conv.reindex k).2

/-- Map on associated graded pieces induced by filtration-compatible maps. -/
noncomputable def Filtration.inducedAssocGradedMap
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
        Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (s : ℤ) (k' : ω') : F₁.associatedGraded s k' ⟶ F₂.associatedGraded s k' :=
  cokernel.map
    (Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k'))
    (Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (hcompat (s + 1) k').choose
    (hcompat s k').choose
    (by
      apply (cancel_mono ((F₂.F s k').arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(hcompat s k').choose_spec, (hcompat (s + 1) k').choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

/-- Data part of a morphism between convergent spectral sequences. -/
structure ConvergenceMorphismData
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂) where
  /-- Map on infinity pages. -/
  eMap : ∀ (k : ω), (E₁.ssData k).eInfty ⟶ (E₂.ssData k).eInfty
  /-- Map on the target graded objects. -/
  aMap : ∀ (k' : ω'), A₁ k' ⟶ A₂ k'
  /-- The target map preserves the filtrations. -/
  filtration_compat : ∀ (s : ℤ) (k' : ω'),
    ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k')),
      φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k'

/-- A morphism between convergent spectral sequences. -/
structure ConvergenceMorphism
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    extends ConvergenceMorphismData conv₁ conv₂ where
  /-- The two reindexings agree. -/
  reindex_eq : conv₁.reindex = conv₂.reindex
  /-- Compatibility with the convergence isomorphisms. -/
  iso_compat : ∀ (k : ω),
    eMap k ≫ (conv₂.iso k).hom ≫
      F₂.transportGraded (congrFun reindex_eq k).symm =
    (conv₁.iso k).hom ≫
      Filtration.inducedAssocGradedMap aMap filtration_compat
        (conv₁.reindex k).1 (conv₁.reindex k).2

/-- A filtration-preserving degreewise map. -/
structure FilteredMorphism
    {ω : Type w} {A₁ A₂ : ω → C} (F₁ : Filtration A₁) (F₂ : Filtration A₂) where
  /-- Degreewise map. -/
  map : ∀ (k : ω), A₁ k ⟶ A₂ k
  /-- Restriction to every filtration level. -/
  compat : ∀ (s : ℤ) (k : ω),
    ∃ (φ : Subobject.underlying.obj (F₁.F s k) ⟶
      Subobject.underlying.obj (F₂.F s k)),
      φ ≫ (F₂.F s k).arrow = (F₁.F s k).arrow ≫ map k

/-- A filtered morphism induces a map of associated graded pieces. -/
noncomputable def FilteredMorphism.inducedGrMap
    {ω : Type w} {A₁ A₂ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (f : FilteredMorphism F₁ F₂) (s : ℤ) (k : ω) :
    F₁.associatedGraded s k ⟶ F₂.associatedGraded s k :=
  Filtration.inducedAssocGradedMap f.map f.compat s k

/-- A spectral sequence packaged with its filtered target and convergence data. -/
structure ConvergingSS
    (C : Type u) [Category.{v} C] [Abelian C]
    (ω : Type w) [AddCommGroup ω] [DecidableEq ω] (ω' : Type w) where
  /-- Underlying spectral sequence. -/
  E : SpectralSequence C ω
  /-- Target graded object. -/
  A : ω' → C
  /-- Filtration on the target. -/
  F : Filtration A
  /-- Convergence identification. -/
  conv : Convergence E A F

/-- Associated-graded map with the restriction maps supplied explicitly. -/
noncomputable def Filtration.inducedGradedMapOfMap
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (φ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k'))
    (hw : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫
          Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (s : ℤ) (k' : ω') : F₁.associatedGraded s k' ⟶ F₂.associatedGraded s k' :=
  cokernel.map
    (Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k'))
    (Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (φ (s + 1) k') (φ s k') (hw s k')

end KIP126.Core.SpectralSequence
