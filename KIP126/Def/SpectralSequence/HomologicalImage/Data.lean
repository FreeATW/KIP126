import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.SpectralObject.Basic

/-!
# Homological image of a triangulated spectral object

Mathlib provides the two sides of this bridge separately: a triangulated
spectral object and the long exact sequence produced by a homological functor.
This file supplies the project-owned conversion between them. -/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows

universe u v

variable {C A ι : Type*} [Category C] [Category ι]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category A] [Abelian A]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Apply a homological functor with a shift sequence to a triangulated
spectral object.  The connecting maps are the homology-sequence connecting
maps, and the three exactness fields are inherited from the distinguished
triangles. -/
noncomputable def homologicalImage
    (T : Triangulated.SpectralObject C ι) (F : C ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject A ι where
  H n := T.ω₁ ⋙ F.shift n
  δ' n₀ n₁ h :=
    { app := fun D => by
        exact F.shiftMap (T.δ'.app D) n₀ n₁ (by rw [add_comm, h])
      naturality := by
        intro D₁ D₂ α
        dsimp [Functor.shiftMap]
        dsimp only [Functor.comp]
        have hH := F.homologySequenceδ_naturality
          (T.ω₂.obj D₁) (T.ω₂.obj D₂) (T.ω₂.map α) n₀ n₁ h
        simpa [Functor.homologySequenceδ, Functor.shiftMap,
          Triangulated.SpectralObject.ω₂] using hH }
  exact₁' n₀ n₁ h D := by
    have hE := F.homologySequence_exact₁
      (T.ω₂.obj D) (T.ω₂_obj_distinguished D) n₀ n₁ h
    simpa [ShortComplex.toComposableArrows, Functor.homologySequenceδ,
      Functor.shiftMap, Triangulated.SpectralObject.ω₂] using
      hE.exact_toComposableArrows

  exact₂' n D := by
    have hE := F.homologySequence_exact₂
      (T.ω₂.obj D) (T.ω₂_obj_distinguished D) n
    simpa [ShortComplex.toComposableArrows, Triangulated.SpectralObject.ω₂] using
      hE.exact_toComposableArrows
  exact₃' n₀ n₁ h D := by
    have hE := F.homologySequence_exact₃
      (T.ω₂.obj D) (T.ω₂_obj_distinguished D) n₀ n₁ h
    simpa [ShortComplex.toComposableArrows, Functor.homologySequenceδ,
      Functor.shiftMap, Triangulated.SpectralObject.ω₂] using
      hE.exact_toComposableArrows

@[simp]
lemma homologicalImage_H (T : Triangulated.SpectralObject C ι) (F : C ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] (n : ℤ) :
    (homologicalImage T F).H n = T.ω₁ ⋙ F.shift n := rfl

@[simp]
lemma homologicalImage_delta_app (T : Triangulated.SpectralObject C ι) (F : C ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological]
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    ((homologicalImage T F).δ' n₀ n₁ h).app D =
      F.homologySequenceδ (T.ω₂.obj D) n₀ n₁ h := rfl

/-- The homological image of Mathlib's mapping-cone spectral object. -/
noncomputable def mappingConeHomologicalImage
    (C A : Type*) [Category C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject A (CochainComplex C ℤ) :=
  homologicalImage (HomotopyCategory.spectralObjectMappingCone C) F

@[simp]
lemma mappingConeHomologicalImage_H (C A : Type*) [Category C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] (n : ℤ) :
    (mappingConeHomologicalImage C A F).H n =
      (HomotopyCategory.spectralObjectMappingCone C).ω₁ ⋙ F.shift n := rfl

/-- The three exactness fields of the homological image can be projected as a
single proposition for downstream bridge statements. -/
theorem homologicalImage_exactness
    (T : Triangulated.SpectralObject C ι) (F : C ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    (∀ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2),
      (mk₂ (((homologicalImage T F).δ' n₀ n₁ h).app D)
        (((homologicalImage T F).H n₁).map
          ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact) ∧
    (∀ (n : ℤ) (D : ComposableArrows ι 2),
      (mk₂ (((homologicalImage T F).H n).map
          ((mapFunctorArrows ι 0 1 0 2 2).app D))
        (((homologicalImage T F).H n).map
          ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact) ∧
    (∀ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2),
      (mk₂ (((homologicalImage T F).H n₀).map
          ((mapFunctorArrows ι 0 2 1 2 2).app D))
        (((homologicalImage T F).δ' n₀ n₁ h).app D)).Exact) := by
  exact ⟨fun n₀ n₁ h D => (homologicalImage T F).exact₁' n₀ n₁ h D,
    fun n D => (homologicalImage T F).exact₂' n D,
    fun n₀ n₁ h D => (homologicalImage T F).exact₃' n₀ n₁ h D⟩

/-- Regression form of the bridge: the mapping-cone specialization exposes all
three exactness obligations without unfolding the spectral-object structure at
each use site. -/
theorem mappingConeHomologicalImage_exactness (C A : Type*) [Category C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [Category A]
    [Abelian A] (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    (∀ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
      (D : ComposableArrows (CochainComplex C ℤ) 2),
      (mk₂ (((mappingConeHomologicalImage C A F).δ' n₀ n₁ h).app D)
        (((mappingConeHomologicalImage C A F).H n₁).map
          ((mapFunctorArrows (CochainComplex C ℤ) 0 1 0 2 2).app D))).Exact) ∧
    (∀ (n : ℤ) (D : ComposableArrows (CochainComplex C ℤ) 2),
      (mk₂ (((mappingConeHomologicalImage C A F).H n).map
          ((mapFunctorArrows (CochainComplex C ℤ) 0 1 0 2 2).app D))
        (((mappingConeHomologicalImage C A F).H n).map
          ((mapFunctorArrows (CochainComplex C ℤ) 0 2 1 2 2).app D))).Exact) ∧
    (∀ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
      (D : ComposableArrows (CochainComplex C ℤ) 2),
      (mk₂ (((mappingConeHomologicalImage C A F).H n₀).map
          ((mapFunctorArrows (CochainComplex C ℤ) 0 2 1 2 2).app D))
        (((mappingConeHomologicalImage C A F).δ' n₀ n₁ h).app D)).Exact) := by
  simpa [mappingConeHomologicalImage] using
    (homologicalImage_exactness (HomotopyCategory.spectralObjectMappingCone C) F)

/-- The connecting transformations in the homological image are natural in
the composable-arrow index. -/
theorem homologicalImage_delta_naturality
    (T : Triangulated.SpectralObject C ι) (F : C ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological]
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∀ {D₁ D₂ : ComposableArrows ι 2} (α : D₁ ⟶ D₂),
      (functorArrows ι 1 2 2 ⋙ (homologicalImage T F).H n₀).map α ≫
          ((homologicalImage T F).δ' n₀ n₁ h).app D₂ =
        ((homologicalImage T F).δ' n₀ n₁ h).app D₁ ≫
          (functorArrows ι 0 1 2 ⋙ (homologicalImage T F).H n₁).map α := by
  intro D₁ D₂ α
  exact ((homologicalImage T F).δ' n₀ n₁ h).naturality α

/-! ### Functoriality -/

/-- A morphism of triangulated spectral objects induces a morphism after taking
the homological image.  The commutative square is exactly the naturality of
the homology-sequence connecting map. -/
noncomputable def homologicalImageHom
    {T U : Triangulated.SpectralObject C ι} (φ : T ⟶ U)
    (F : C ⥤ A) [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject.Hom (homologicalImage T F) (homologicalImage U F) where
  hom n := Functor.whiskerRight φ.hom (F.shift n)
  comm n₀ n₁ hn {i j k} f g := by
    change F.shiftMap (T.δ f g) n₀ n₁ _ ≫
        (F.shift n₁).map (φ.hom.app (ComposableArrows.mk₁ f)) =
      (F.shift n₀).map (φ.hom.app (ComposableArrows.mk₁ g)) ≫
        F.shiftMap (U.δ f g) n₀ n₁ _
    rw [← F.shiftMap_comp, φ.comm, F.shiftMap_comp']

/-- The homological-image bridge is functorial in the triangulated spectral
object. -/
noncomputable def homologicalImageFunctor
    (F : C ⥤ A) [F.ShiftSequence ℤ] [F.IsHomological] :
    Triangulated.SpectralObject C ι ⥤ Abelian.SpectralObject A ι where
  obj T := homologicalImage T F
  map φ := homologicalImageHom φ F
  map_id := by
    intro T
    apply Abelian.SpectralObject.Hom.ext
    funext n
    apply NatTrans.ext
    funext D
    simp [homologicalImageHom]
  map_comp φ ψ := by
    apply Abelian.SpectralObject.Hom.ext
    funext n
    apply NatTrans.ext
    funext D
    simp [homologicalImageHom]

end KIP126.Core.SpectralSequence
