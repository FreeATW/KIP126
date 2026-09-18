import KIP126.Def.SpectralSequence.FilteredComplex.Data
import KIP126.Def.SpectralSequence.HomologicalImage.Data

/-!
# Spectral-object adapter for filtered complexes

The filtered-complex layer provides a diagram of integer-indexed cochain
complexes.  Mathlib's mapping-cone spectral object is indexed by cochain
complexes, so precomposition turns that diagram into a triangulated spectral
object.  The project-owned homological-image bridge then supplies the
corresponding abelian spectral object.  Convergence and endpoint hypotheses
are intentionally not inferred by this adapter; they remain explicit inputs
to the later spectral-sequence construction.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Precomposition on spectral objects -/

noncomputable def spectralObjectMapComposableArrows
    {ι J : Type*} [Category ι] [Category J]
    {D E : ι ⥤ J} (α : D ⟶ E) (n : ℕ) :
    D.mapComposableArrows n ⟶ E.mapComposableArrows n :=
  (Functor.whiskeringRight (Fin (n + 1)) ι J).map α

noncomputable def spectralObjectArrowMap
    {ι J : Type*} [Category ι] [Category J]
    {D E : ι ⥤ J} (α : D ⟶ E) {X Y : ι} (f : X ⟶ Y) :
    ComposableArrows.mk₁ (D.map f) ⟶ ComposableArrows.mk₁ (E.map f) :=
  ComposableArrows.homMk₁ (α.app X) (α.app Y) (α.naturality f)

lemma spectralObjectMapComposableArrows_one_app
    {ι J : Type*} [Category ι] [Category J]
    {D E : ι ⥤ J} (α : D ⟶ E) {X Y : ι} (f : X ⟶ Y) :
    (D.mapComposableArrowsObjMk₁Iso f).hom ≫ spectralObjectArrowMap α f =
      (spectralObjectMapComposableArrows α 1).app
          (ComposableArrows.mk₁ f) ≫
        (E.mapComposableArrowsObjMk₁Iso f).hom := by
  apply ComposableArrows.hom_ext₁
  · change 𝟙 _ ≫ α.app X = α.app X ≫ 𝟙 _
    simp
  · change 𝟙 _ ≫ α.app Y = α.app Y ≫ 𝟙 _
    simp

noncomputable def spectralObjectPrecompHom
    {K J ι : Type*} [Category K] [HasZeroObject K] [HasShift K ℤ]
    [Preadditive K] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K] [Category J] [Category ι]
    (T : Triangulated.SpectralObject K J)
    {D E : ι ⥤ J} (α : D ⟶ E) :
    Triangulated.SpectralObject.Hom (T.precomp D) (T.precomp E) where
  hom := Functor.whiskerRight (spectralObjectMapComposableArrows α 1) T.ω₁
  comm {i j k} f g := by
    dsimp [Triangulated.SpectralObject.precomp, Triangulated.SpectralObject.δ]
    have hδ := T.δ'.naturality
      ((spectralObjectMapComposableArrows α 2).app
        (ComposableArrows.mk₂ f g))
    dsimp at hδ
    simp [spectralObjectMapComposableArrows, ComposableArrows.functorArrows,
      Functor.mapComposableArrows] at hδ
    have hδ' :
        T.ω₁.map (spectralObjectArrowMap α g) ≫
            T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) =
          T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            (shiftFunctor K 1).map (T.ω₁.map (spectralObjectArrowMap α f)) := by
      convert hδ using 1 <;> rfl
    have hcomp_f := spectralObjectMapComposableArrows_one_app α f
    have hcomp_g := spectralObjectMapComposableArrows_one_app α g
    have hcomp_f' :
        (D.mapComposableArrowsObjMk₁Iso f).inv ≫
            (spectralObjectMapComposableArrows α 1).app
              (ComposableArrows.mk₁ f) =
          spectralObjectArrowMap α f ≫ (E.mapComposableArrowsObjMk₁Iso f).inv := by
      rw [← cancel_mono (E.mapComposableArrowsObjMk₁Iso f).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← hcomp_f]
      simp
    have hcomp_g' :
        (D.mapComposableArrowsObjMk₁Iso g).hom ≫ spectralObjectArrowMap α g =
          (spectralObjectMapComposableArrows α 1).app
            (ComposableArrows.mk₁ g) ≫
            (E.mapComposableArrowsObjMk₁Iso g).hom := hcomp_g
    have hcomp_f_map :
        T.ω₁.map ((D.mapComposableArrowsObjMk₁Iso f).inv ≫
          (spectralObjectMapComposableArrows α 1).app (ComposableArrows.mk₁ f)) =
          T.ω₁.map (spectralObjectArrowMap α f ≫
            (E.mapComposableArrowsObjMk₁Iso f).inv) := by
      exact congrArg (fun q => T.ω₁.map q) hcomp_f'
    have hcomp_g_map :
        T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            T.ω₁.map (spectralObjectArrowMap α g) =
          T.ω₁.map ((spectralObjectMapComposableArrows α 1).app
            (ComposableArrows.mk₁ g)) ≫
            T.ω₁.map (E.mapComposableArrowsObjMk₁Iso g).hom := by
      rw [← Functor.map_comp, hcomp_g']
      rw [Functor.map_comp]
    have hshift_f :
        (shiftFunctor K (1 : ℤ)).map
            (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso f).inv) ≫
            (shiftFunctor K (1 : ℤ)).map
              (T.ω₁.map ((spectralObjectMapComposableArrows α 1).app
                (ComposableArrows.mk₁ f))) =
          (shiftFunctor K (1 : ℤ)).map
            (T.ω₁.map ((D.mapComposableArrowsObjMk₁Iso f).inv ≫
              (spectralObjectMapComposableArrows α 1).app
                (ComposableArrows.mk₁ f))) := by
      rw [← Functor.map_comp]
      rw [← Functor.map_comp]
    have hshift_f_assoc :
        T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
              ((shiftFunctor K (1 : ℤ)).map
                  (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso f).inv) ≫
                (shiftFunctor K (1 : ℤ)).map
                  (T.ω₁.map ((spectralObjectMapComposableArrows α 1).app
                    (ComposableArrows.mk₁ f))))) =
          T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
              (shiftFunctor K (1 : ℤ)).map
                (T.ω₁.map ((D.mapComposableArrowsObjMk₁Iso f).inv ≫
                  (spectralObjectMapComposableArrows α 1).app
                    (ComposableArrows.mk₁ f)))) := by
      convert congrArg (fun q =>
        T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫ q)
        hshift_f using 1 <;> rfl
    have hcomp_f_assoc :
        T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
              (shiftFunctor K (1 : ℤ)).map
                (T.ω₁.map ((D.mapComposableArrowsObjMk₁Iso f).inv ≫
                  (spectralObjectMapComposableArrows α 1).app
                    (ComposableArrows.mk₁ f)))) =
          T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
              (shiftFunctor K (1 : ℤ)).map
                (T.ω₁.map (spectralObjectArrowMap α f ≫
                  (E.mapComposableArrowsObjMk₁Iso f).inv))) := by
      convert congrArg (fun q =>
        T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
          (shiftFunctor K (1 : ℤ)).map q) hcomp_f_map using 1 <;> rfl
    have hsplit_f :
        (shiftFunctor K (1 : ℤ)).map
            (T.ω₁.map (spectralObjectArrowMap α f ≫
              (E.mapComposableArrowsObjMk₁Iso f).inv)) =
          (shiftFunctor K (1 : ℤ)).map (T.ω₁.map (spectralObjectArrowMap α f)) ≫
            (shiftFunctor K (1 : ℤ)).map
              (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv) := by
      simp only [Functor.map_comp]
    have hsplit_f_assoc :
        T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
              (shiftFunctor K (1 : ℤ)).map
                (T.ω₁.map (spectralObjectArrowMap α f ≫
                  (E.mapComposableArrowsObjMk₁Iso f).inv))) =
          T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
              ((shiftFunctor K (1 : ℤ)).map (T.ω₁.map (spectralObjectArrowMap α f)) ≫
                (shiftFunctor K (1 : ℤ)).map
                  (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv))) := by
      convert congrArg (fun q =>
        T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫ q)
        hsplit_f using 1 <;> rfl
    have hδ_assoc :
        (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
              (shiftFunctor K (1 : ℤ)).map (T.ω₁.map (spectralObjectArrowMap α f)))) ≫
            (shiftFunctor K (1 : ℤ)).map
              (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv) =
          (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            (T.ω₁.map (spectralObjectArrowMap α g) ≫
              T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)))) ≫
            (shiftFunctor K (1 : ℤ)).map
              (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv) := by
      exact congrArg (fun q =>
        (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫ q) ≫
          (shiftFunctor K (1 : ℤ)).map
            (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv)) hδ'.symm
    have hcomp_g_assoc :
        (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            T.ω₁.map (spectralObjectArrowMap α g)) ≫
          T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            (shiftFunctor K (1 : ℤ)).map
              (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv) =
          (T.ω₁.map ((spectralObjectMapComposableArrows α 1).app
              (ComposableArrows.mk₁ g)) ≫
            T.ω₁.map (E.mapComposableArrowsObjMk₁Iso g).hom) ≫
          T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            (shiftFunctor K (1 : ℤ)).map
              (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv) := by
      exact congrArg (fun q =>
        q ≫ T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
          (shiftFunctor K (1 : ℤ)).map
            (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv)) hcomp_g_map
    change
      (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
          (shiftFunctor K 1).map
            (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso f).inv)) ≫
        (shiftFunctor K 1).map
          (T.ω₁.map ((spectralObjectMapComposableArrows α 1).app
            (ComposableArrows.mk₁ f))) =
      T.ω₁.map ((spectralObjectMapComposableArrows α 1).app
        (ComposableArrows.mk₁ g)) ≫
        T.ω₁.map (E.mapComposableArrowsObjMk₁Iso g).hom ≫
          T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
          (shiftFunctor K 1).map
            (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv)
    calc
      _ = T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            ((shiftFunctor K 1).map (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso f).inv) ≫
              (shiftFunctor K 1).map
                (T.ω₁.map ((spectralObjectMapComposableArrows α 1).app
                  (ComposableArrows.mk₁ f)))) ) := by
            simp only [Category.assoc]
      _ = T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            (shiftFunctor K 1).map
              (T.ω₁.map ((D.mapComposableArrowsObjMk₁Iso f).inv ≫
                (spectralObjectMapComposableArrows α 1).app
                  (ComposableArrows.mk₁ f)))) := by
            exact hshift_f_assoc
      _ = T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            (shiftFunctor K 1).map
              (T.ω₁.map (spectralObjectArrowMap α f ≫
                (E.mapComposableArrowsObjMk₁Iso f).inv))) := by
            exact hcomp_f_assoc
      _ = T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          (T.δ'.app ((D.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            ((shiftFunctor K 1).map (T.ω₁.map (spectralObjectArrowMap α f)) ≫
              (shiftFunctor K 1).map
                (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv))) := by
            exact hsplit_f_assoc
      _ = T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
          (T.ω₁.map (spectralObjectArrowMap α g) ≫
            T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            (shiftFunctor K 1).map
              (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv)) := by
            simpa only [Category.assoc] using hδ_assoc
      _ = (T.ω₁.map (D.mapComposableArrowsObjMk₁Iso g).hom ≫
            T.ω₁.map (spectralObjectArrowMap α g)) ≫
          T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            (shiftFunctor K 1).map
              (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv) := by
            simp only [Category.assoc]
      _ = T.ω₁.map ((spectralObjectMapComposableArrows α 1).app
          (ComposableArrows.mk₁ g)) ≫
          T.ω₁.map (E.mapComposableArrowsObjMk₁Iso g).hom ≫
          T.δ'.app ((E.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g)) ≫
            (shiftFunctor K 1).map
              (T.ω₁.map (E.mapComposableArrowsObjMk₁Iso f).inv) := by
            simpa only [Category.assoc] using hcomp_g_assoc

/-- The mapping-cone spectral object precomposed with a cochain diagram. -/
noncomputable def cochainDiagramTriangulatedSpectralObject
    {ι : Type*} [Category ι] (D : ι ⥤ CochainComplex C ℤ) :
    Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) ι :=
  (HomotopyCategory.spectralObjectMappingCone C).precomp D

/-- The filtered-complex instance of the triangulated adapter. -/
noncomputable def filteredComplexTriangulatedSpectralObject
    (FC : FilteredComplex C) :
    Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) (OrderDual ℤ) :=
  cochainDiagramTriangulatedSpectralObject FC.filteredCochainDiagram

@[simp]
lemma filteredComplexTriangulatedSpectralObject_ω₁
    (FC : FilteredComplex C) :
    (filteredComplexTriangulatedSpectralObject FC).ω₁ =
      (FC.filteredCochainDiagram.mapComposableArrows 1) ⋙
        (HomotopyCategory.spectralObjectMappingCone C).ω₁ := rfl

/-- The natural transformation on cochain diagrams induces a morphism of the
precomposed triangulated spectral objects. -/
noncomputable def cochainDiagramTriangulatedSpectralObjectHom
    {ι : Type*} [Category ι]
    {D E : ι ⥤ CochainComplex C ℤ} (α : D ⟶ E) :
    Triangulated.SpectralObject.Hom
      (cochainDiagramTriangulatedSpectralObject D)
      (cochainDiagramTriangulatedSpectralObject E) :=
  spectralObjectPrecompHom
    (HomotopyCategory.spectralObjectMappingCone C) α

/-- The cochain-diagram triangulated adapter is a functor. -/
noncomputable def cochainDiagramTriangulatedSpectralObjectFunctor
    {ι : Type*} [Category ι] :
    (ι ⥤ CochainComplex C ℤ) ⥤
      Triangulated.SpectralObject
        (HomotopyCategory C (ComplexShape.up ℤ)) ι where
  obj D := cochainDiagramTriangulatedSpectralObject D
  map α := cochainDiagramTriangulatedSpectralObjectHom α
  map_id D := by
    apply Triangulated.SpectralObject.Hom.ext
    apply NatTrans.ext
    funext X
    change (HomotopyCategory.spectralObjectMappingCone C).ω₁.map (𝟙 _) = 𝟙 _
    simp
  map_comp := by
    intro D E G α β
    apply Triangulated.SpectralObject.Hom.ext
    apply NatTrans.ext
    funext X
    change (HomotopyCategory.spectralObjectMappingCone C).ω₁.map
        (((Functor.whiskeringRight (Fin 2) ι (CochainComplex C ℤ)).map α).app X ≫
          ((Functor.whiskeringRight (Fin 2) ι (CochainComplex C ℤ)).map β).app X) =
      (HomotopyCategory.spectralObjectMappingCone C).ω₁.map
          (((Functor.whiskeringRight (Fin 2) ι (CochainComplex C ℤ)).map α).app X) ≫
        (HomotopyCategory.spectralObjectMappingCone C).ω₁.map
          (((Functor.whiskeringRight (Fin 2) ι (CochainComplex C ℤ)).map β).app X)
    rw [Functor.map_comp]

/-- The filtered-complex triangulated adapter, including its maps. -/
noncomputable def filteredComplexTriangulatedSpectralObjectHom
    {FC GD : FilteredComplex C} (f : FC ⟶ GD) :
    Triangulated.SpectralObject.Hom
      (filteredComplexTriangulatedSpectralObject FC)
      (filteredComplexTriangulatedSpectralObject GD) :=
  cochainDiagramTriangulatedSpectralObjectHom
    f.filteredCochainDiagramNatTrans

noncomputable def filteredComplexTriangulatedSpectralObjectFunctor :
    FilteredComplex C ⥤
      Triangulated.SpectralObject
        (HomotopyCategory C (ComplexShape.up ℤ)) (OrderDual ℤ) :=
  FilteredComplex.filteredCochainDiagramFunctor ⋙
    cochainDiagramTriangulatedSpectralObjectFunctor

/-- Apply a homological functor and its shift sequence to a cochain diagram. -/
noncomputable def cochainDiagramHomologicalImage
    {ι : Type*} [Category ι] (D : ι ⥤ CochainComplex C ℤ)
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject A ι :=
  homologicalImage (cochainDiagramTriangulatedSpectralObject D) F

/-- The abelian spectral object associated to a filtered complex. -/
noncomputable def filteredComplexAbelianSpectralObject
    (FC : FilteredComplex C) (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject A (OrderDual ℤ) :=
  cochainDiagramHomologicalImage FC.filteredCochainDiagram A F

/-- The abelian adapter is functorial in a natural transformation of cochain
diagrams. -/
noncomputable def cochainDiagramHomologicalImageHom
    {ι : Type*} [Category ι] (D E : ι ⥤ CochainComplex C ℤ)
    (α : D ⟶ E) (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject.Hom
      (cochainDiagramHomologicalImage D A F)
      (cochainDiagramHomologicalImage E A F) :=
  homologicalImageHom (cochainDiagramTriangulatedSpectralObjectHom α) F

noncomputable def cochainDiagramHomologicalImageFunctor
    {ι : Type*} [Category ι] (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    (ι ⥤ CochainComplex C ℤ) ⥤ Abelian.SpectralObject A ι :=
  cochainDiagramTriangulatedSpectralObjectFunctor ⋙ homologicalImageFunctor F

noncomputable def filteredComplexAbelianSpectralObjectHom
    {FC GD : FilteredComplex C} (f : FC ⟶ GD)
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject.Hom
      (filteredComplexAbelianSpectralObject FC A F)
      (filteredComplexAbelianSpectralObject GD A F) :=
  cochainDiagramHomologicalImageHom FC.filteredCochainDiagram
    GD.filteredCochainDiagram f.filteredCochainDiagramNatTrans A F

noncomputable def filteredComplexAbelianSpectralObjectFunctor
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    FilteredComplex C ⥤ Abelian.SpectralObject A (OrderDual ℤ) :=
  filteredComplexTriangulatedSpectralObjectFunctor ⋙ homologicalImageFunctor F

@[simp]
lemma cochainDiagramHomologicalImage_H
    {ι : Type*} [Category ι] (D : ι ⥤ CochainComplex C ℤ)
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] (n : ℤ) :
    (cochainDiagramHomologicalImage D A F).H n =
      (cochainDiagramTriangulatedSpectralObject D).ω₁ ⋙ F.shift n := rfl

@[simp]
lemma filteredComplexAbelianSpectralObject_H
    (FC : FilteredComplex C) (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] (n : ℤ) :
    (filteredComplexAbelianSpectralObject FC A F).H n =
      (filteredComplexTriangulatedSpectralObject FC).ω₁ ⋙ F.shift n := rfl

end KIP126.Core.SpectralSequence
