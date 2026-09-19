import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Stable-homotopy context interfaces

The Adams layer below still uses the small `StableHomotopyContext` record at the
end of this file.  The category-theoretic interface here is a separate, more
faithful port of the stable-homotopy definitions: it packages the structure a
concrete homotopy category must provide, while leaving construction-specific
choices (such as a functorial cofiber or a closed structure) as explicit data.
No global instance or theorem is postulated by this file.
-/

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory Pretriangulated

universe u v

/-- The structural part of a stable homotopy category.

The fields are bundled so a concrete model can supply its additive, shifted,
monoidal, and triangulated structures together.  In particular, this class
does not assert the extra closedness, cofiber choices, or sign conventions
used by particular constructions; those belong to separate witness records.
-/
class StableHomotopyCategory (C : Type u) extends
    Category.{v} C,
    Preadditive C,
    HasShift C ℤ,
    MonoidalCategory C where
  /-- Every shift functor is additive. -/
  shiftAdditive : ∀ (n : ℤ), (shiftFunctor C n).Additive
  /-- The category has a zero object. -/
  hasZeroObject : HasZeroObject C
  /-- The category is pretriangulated. -/
  pretriangulated : Pretriangulated C

attribute [instance] StableHomotopyCategory.shiftAdditive
attribute [instance] StableHomotopyCategory.hasZeroObject
attribute [instance] StableHomotopyCategory.pretriangulated
attribute [reducible] StableHomotopyCategory.pretriangulated

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-! ### Explicit cofiber and tensor-triangulated witnesses -/

/-- A chosen functorial cofiber construction on a stable category.

This is data supplied by a concrete model.  Keeping it as a class preserves
the convenient Mathlib notation without introducing a global postulate that
would silently choose a cofiber for every map.
-/
class HasFunctorialCofiber where
  cofib : {X Y : C} → (X ⟶ Y) → C
  cofibι : {X Y : C} → (f : X ⟶ Y) → Y ⟶ cofib f
  cofibδ : {X Y : C} → (f : X ⟶ Y) → cofib f ⟶ (shiftFunctor C (1 : ℤ)).obj X
  cofib_distinguished : ∀ {X Y : C} (f : X ⟶ Y),
    Triangle.mk f (cofibι f) (cofibδ f) ∈ distTriang C
  cofibMap : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂), α ≫ f₂ = f₁ ≫ β →
    (cofib f₁ ⟶ cofib f₂)
  cofibMap_ι : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β),
    β ≫ cofibι f₂ = cofibι f₁ ≫ cofibMap f₁ f₂ α β h
  cofibMap_δ : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β),
    cofibMap f₁ f₂ α β h ≫ cofibδ f₂ =
      cofibδ f₁ ≫ (shiftFunctor C (1 : ℤ)).map α

/-- A functorial cofiber compatible with tensoring on the right. -/
class TensorTriangulatedCatWithFunctorialCofiber extends HasFunctorialCofiber (C := C) where
  tensorCofibIso : ∀ {X Y : C} (f : X ⟶ Y) (W : C),
    HasFunctorialCofiber.cofib (f ▷ W) ≅ HasFunctorialCofiber.cofib f ⊗ W

/-- Closed symmetric tensor-triangulated compatibility data.

The exactness and suspension fields are hypotheses of a chosen model, rather
than global theorems of the abstract category interface.
-/
class ClosedSymmetricTensorTriangulated where
  symmetricCategory : SymmetricCategory C
  monoidalClosed : MonoidalClosed C
  smashSuspIso : ∀ (X Y : C),
    (shiftFunctor C (1 : ℤ)).obj X ⊗ Y ≅
      (shiftFunctor C (1 : ℤ)).obj (X ⊗ Y)
  smashExact : ∀ (W : C) [_inst : (tensorRight W).CommShift ℤ]
    (T : Triangle C), T ∈ distTriang C →
    (tensorRight W).mapTriangle.obj T ∈ distTriang C
  ihomExact : ∀ (W : C),
    letI : MonoidalClosed C := monoidalClosed
    ∀ [_inst : (ihom W).CommShift ℤ],
      (T : Triangle C) → T ∈ distTriang C →
      (ihom W).mapTriangle.obj T ∈ distTriang C

attribute [instance] ClosedSymmetricTensorTriangulated.symmetricCategory
attribute [instance] ClosedSymmetricTensorTriangulated.monoidalClosed

/-- The internal mapping spectrum supplied by a closed monoidal witness. -/
noncomputable def MappingSpectrum (X Y : C)
    [ClosedSymmetricTensorTriangulated (C := C)] : C :=
  (ihom X).obj Y

/-- The sphere spectrum is the monoidal unit. -/
abbrev SphereSpectrum : C := 𝟙_ C

/-- The `n`-sphere is the `n`-fold shift of the sphere spectrum. -/
abbrev Sphere (n : ℤ) : C := (shiftFunctor C n).obj SphereSpectrum

/-- Stable homotopy classes represented by maps from the `n`-sphere. -/
abbrev HomotopyGroup (n : ℤ) (X : C) : Type v := Sphere n ⟶ X

/-- The graded homotopy groups of a spectrum, as additive-group objects. -/
noncomputable def HomotopyGroups (X : C) : ℤ → AddCommGrpCat.{v} :=
  fun n => AddCommGrpCat.mk (HomotopyGroup n X)

/-! ### Distinguished cofiber triangles and induced maps -/

/-- A chosen distinguished triangle `X → Y → Z → ΣX`. -/
structure HoCofiberSequence where
  X : C
  Y : C
  Z : C
  f : X ⟶ Y
  g : Y ⟶ Z
  h : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X
  distinguished : Triangle.mk f g h ∈ distTriang C

/-- The map on homotopy groups induced by postcomposition with `f`. -/
def inducedMap {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    HomotopyGroup n X →+ HomotopyGroup n Y where
  toFun := fun α => α ≫ f
  map_zero' := Limits.zero_comp
  map_add' := fun a b => Preadditive.add_comp _ _ _ a b f

end KIP126.StableHomotopy

namespace KIP126.Classical.Adams

/-- The stable-homotopy operations used by the domain layer.  No homotopy
groups or multiplication are assumed here. -/
structure StableHomotopyContext where
  Spectrum : Type
  sphere : Spectrum
  smash : Spectrum → Spectrum → Spectrum

end KIP126.Classical.Adams
