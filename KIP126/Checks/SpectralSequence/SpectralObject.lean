import KIP126.Def.SpectralSequence.SpectralObject.Data
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Regression checks for the spectral-object adapter

These examples deliberately remain small: compiling the declarations checks
that both the triangulated and abelian morphism layers are available, and that
the generic homological-image adapter can be specialized to Mathlib's usual
module-valued homology functor.
-/

namespace KIP126.Core.SpectralSequence

noncomputable section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

section Triangulated

variable {ι : Type*} [Category ι]
variable {D E : ι ⥤ CochainComplex C ℤ} (α : D ⟶ E)

example :
    cochainDiagramTriangulatedSpectralObject D ⟶
      cochainDiagramTriangulatedSpectralObject E :=
  cochainDiagramTriangulatedSpectralObjectHom α

example :
    (cochainDiagramTriangulatedSpectralObjectFunctor (C := C)).map α =
      cochainDiagramTriangulatedSpectralObjectHom α := rfl

example :
    (ι ⥤ CochainComplex C ℤ) ⥤
      Triangulated.SpectralObject
        (HomotopyCategory C (ComplexShape.up ℤ)) ι :=
  cochainDiagramTriangulatedSpectralObjectFunctor

end Triangulated

section Abelian

variable {ι : Type*} [Category ι]
variable {A : Type*} [Category A] [Abelian A]
variable (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
variable [F.ShiftSequence ℤ] [F.IsHomological]
variable {D E : ι ⥤ CochainComplex C ℤ} (α : D ⟶ E)

example :
    cochainDiagramHomologicalImage D A F ⟶
      cochainDiagramHomologicalImage E A F :=
  cochainDiagramHomologicalImageHom D E α A F

example :
    (cochainDiagramHomologicalImageFunctor (C := C) A F).map α =
      cochainDiagramHomologicalImageHom D E α A F := rfl

example :
    (ι ⥤ CochainComplex C ℤ) ⥤ Abelian.SpectralObject A ι :=
  cochainDiagramHomologicalImageFunctor (C := C) A F

end Abelian

section Filtered

variable {FC GD : FilteredComplex C} (f : FC ⟶ GD)

example :
    filteredComplexTriangulatedSpectralObject FC ⟶
      filteredComplexTriangulatedSpectralObject GD :=
  filteredComplexTriangulatedSpectralObjectHom f

example :
    (filteredComplexTriangulatedSpectralObjectFunctor (C := C)).map f =
      filteredComplexTriangulatedSpectralObjectHom f := rfl

variable {A : Type*} [Category A] [Abelian A]
variable (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
variable [F.ShiftSequence ℤ] [F.IsHomological]

example :
    filteredComplexAbelianSpectralObject FC A F ⟶
      filteredComplexAbelianSpectralObject GD A F :=
  filteredComplexAbelianSpectralObjectHom f A F

example :
    (filteredComplexAbelianSpectralObjectFunctor (C := C) A F).map f =
      filteredComplexAbelianSpectralObjectHom f A F := rfl

example :
    FilteredComplex C ⥤ Abelian.SpectralObject A (OrderDual ℤ) :=
  filteredComplexAbelianSpectralObjectFunctor (C := C) A F

end Filtered

section ConcreteSpecialization

example (D : Discrete Unit ⥤ CochainComplex (ModuleCat ℤ) ℤ) :
    Abelian.SpectralObject (ModuleCat ℤ) (Discrete Unit) :=
  cochainDiagramHomologicalImage D (ModuleCat ℤ)
    (HomotopyCategory.homologyFunctor (ModuleCat ℤ)
      (ComplexShape.up ℤ) 0)

end ConcreteSpecialization

end

end KIP126.Core.SpectralSequence
