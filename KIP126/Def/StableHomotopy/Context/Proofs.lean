import KIP126.Def.StableHomotopy.Context.Data

/-! Derived facts for the stable-homotopy category interface. -/
namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory Pretriangulated

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

@[simp] theorem sphereSpectrum_eq_unit :
    (SphereSpectrum : C) = 𝟙_ C := rfl

/-- Build the chosen triangle associated with a map when a concrete model
supplies functorial cofiber data. -/
def HoCofiberSequence.ofMorphism {X Y : C} (f : X ⟶ Y)
    [HasFunctorialCofiber (C := C)] : HoCofiberSequence (C := C) where
  X := X
  Y := Y
  Z := HasFunctorialCofiber.cofib f
  f := f
  g := HasFunctorialCofiber.cofibι f
  h := HasFunctorialCofiber.cofibδ f
  distinguished := HasFunctorialCofiber.cofib_distinguished f

/-- The first two maps in a chosen cofiber triangle compose to zero. -/
theorem HoCofiberSequence.fg_zero (T : HoCofiberSequence (C := C)) :
    T.f ≫ T.g = 0 :=
  comp_distTriang_mor_zero₁₂ _ T.distinguished

/-- The last two maps in a chosen cofiber triangle compose to zero. -/
theorem HoCofiberSequence.gh_zero (T : HoCofiberSequence (C := C)) :
    T.g ≫ T.h = 0 :=
  comp_distTriang_mor_zero₂₃ _ T.distinguished

/-- The connecting map composes trivially with the shifted first map. -/
theorem HoCofiberSequence.hf_shift_zero (T : HoCofiberSequence (C := C)) :
    T.h ≫ (shiftFunctor C (1 : ℤ)).map T.f = 0 :=
  comp_distTriang_mor_zero₃₁ _ T.distinguished

/-- Homotopy groups are functorial in the spectrum variable. -/
noncomputable def homotopyGroupFunctor (n : ℤ) :
    C ⥤ AddCommGrpCat.{v} where
  obj := fun X => AddCommGrpCat.mk (HomotopyGroup n X)
  map := fun f => AddCommGrpCat.ofHom (inducedMap f n)
  map_id := by
    intro X
    apply AddCommGrpCat.hom_ext
    ext x
    simp [inducedMap]
  map_comp := by
    intro X Y Z f g
    apply AddCommGrpCat.hom_ext
    ext x
    simp [inducedMap, Category.assoc]

end KIP126.StableHomotopy
