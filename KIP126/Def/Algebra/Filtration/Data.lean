import KIP126.Def.Algebra.Graded.Data
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Filtered graded objects

This file supplies the part of the shared Core that is not already a Mathlib
object: decreasing filtrations by subobjects of a graded object, their
associated graded pieces, and filtration-preserving maps.  Filtrations and
filtered maps work in an arbitrary category; quotient-based associated graded
pieces work in an abelian category.  Neither layer assumes a field or an
elementwise presentation.
-/

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A decreasing filtration of a graded object.  `F s i` denotes the
subobject $F^s A_i$, and `decreasing` says $F^{s+1} A_i \le F^s A_i$. -/
structure Filtration {ι : Type w} (A : CategoryTheory.GradedObject ι C) where
  /-- The filtration subobject at a filtration level and grading index. -/
  F : ℤ → (i : ι) → Subobject (A i)
  /-- The filtration is decreasing. -/
  decreasing : ∀ (s : ℤ) (i : ι), F (s + 1) i ≤ F s i

namespace Filtration

variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

/-! ### Maps between arbitrary filtration levels

The successor inequality in `Filtration.decreasing` is the compact datum from
which all of the maps in the filtration diagram are obtained.  Keeping this
construction here (rather than re-proving it in the filtered-complex layer)
also fixes the variance convention once and for all: for `t ≤ s`, the
decreasing filtration has an inclusion `F s ↪ F t`.
-/

/-- Monotonicity of a decreasing filtration at arbitrary integer levels. -/
lemma le_of_le (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.F s i ≤ F.F t i := by
  induction s, h using Int.leInduction with
  | base => exact le_rfl
  | succ s _ ih =>
      exact (F.decreasing s i).trans ih

/-- The canonical inclusion `Fˢ Aᵢ ⟶ Fᵗ Aᵢ` when `t ≤ s`. -/
noncomputable def inclusion (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    Subobject.underlying.obj (F.F s i) ⟶ Subobject.underlying.obj (F.F t i) :=
  Subobject.ofLE (F.F s i) (F.F t i) (F.le_of_le h i)

@[simp]
lemma inclusion_arrow (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.inclusion h i ≫ (F.F t i).arrow = (F.F s i).arrow :=
  Subobject.ofLE_arrow _

@[simp]
lemma inclusion_refl (F : Filtration A) (s : ℤ) (i : ι) :
    F.inclusion (le_rfl : s ≤ s) i = 𝟙 _ := by
  simp [inclusion]

@[reassoc (attr := simp)]
lemma inclusion_comp (F : Filtration A) {r s t : ℤ}
    (hrs : r ≤ s) (hst : s ≤ t) (i : ι) :
    F.inclusion hst i ≫ F.inclusion hrs i = F.inclusion (hrs.trans hst) i := by
  simp [inclusion]

/-- Naturality of a filtration subobject arrow under an equality of grading
indices.  This is the transport lemma needed whenever a complex shape writes
the predecessor as an expression such as `(k + 1) - 1`. -/
lemma transport_arrow (F : Filtration A) (s : ℤ) {i j : ι} (h : i = j) :
    eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F s k)) h) ≫
        (F.F s j).arrow =
      (F.F s i).arrow ≫ eqToHom (congrArg A h) := by
  subst h
  simp

/-- The level inclusions are natural with respect to index transports. -/
lemma inclusion_naturality (F : Filtration A) {t s : ℤ} (h : t ≤ s)
    {i j : ι} (hij : i = j) :
    F.inclusion h i ≫
        eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F t k)) hij) =
      eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F s k)) hij) ≫
        F.inclusion h j := by
  subst hij
  simp


/-- The associated graded piece
$\operatorname{gr}^s_F A_i = F^s A_i/F^{s+1} A_i$. -/
noncomputable def associatedGraded [Abelian C] (F : Filtration A) (s : ℤ) (i : ι) : C :=
  cokernel (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.decreasing s i))

/-- The quotient map from a filtration level to its associated graded piece. -/
noncomputable def toAssociatedGraded [Abelian C] (F : Filtration A) (s : ℤ) (i : ι) :
    Subobject.underlying.obj (F.F s i) ⟶ F.associatedGraded s i :=
  cokernel.π (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.decreasing s i))

/-- All associated graded pieces, graded by filtration degree and the original
grading index. -/
noncomputable def associatedGradedObject [Abelian C] (F : Filtration A) :
    CategoryTheory.GradedObject (ℤ × ι) C :=
  fun si => F.associatedGraded si.1 si.2

/-! ### Index transport for associated graded pieces

The associated graded object is indexed by a product, so equal reindexings
must be transported explicitly when a construction changes the presentation
of a bidegree.  This is the canonical replacement for the corresponding
transport helper in the historical convergence file. -/

/-- Transport an associated-graded piece along an equality of its indices. -/
noncomputable def transportGraded [Abelian C] (F : Filtration A)
    {r₁ r₂ : ℤ × ι} (h : r₁ = r₂) :
    F.associatedGraded r₁.1 r₁.2 ⟶ F.associatedGraded r₂.1 r₂.2 :=
  eqToHom (by rw [h])

end Filtration

/-- A morphism of filtered graded objects is a graded map whose restriction to
each filtration subobject factors through the corresponding target
subobject. -/
structure FilteredMorphism {ι : Type w}
    {A B : CategoryTheory.GradedObject ι C} (F : Filtration A) (G : Filtration B) where
  /-- The underlying degree-preserving map. -/
  map : A ⟶ B
  /-- Preservation of every filtration level. -/
  preserves : ∀ (s : ℤ) (i : ι),
    ∃ φ : Subobject.underlying.obj (F.F s i) ⟶ Subobject.underlying.obj (G.F s i),
      φ ≫ (G.F s i).arrow = (F.F s i).arrow ≫ map i

namespace FilteredMorphism

variable {ι : Type w}
  {A B D : CategoryTheory.GradedObject ι C}
  {F : Filtration A} {G : Filtration B} {H : Filtration D}

/-- The identity map of a filtered graded object. -/
def id (F : Filtration A) : FilteredMorphism F F where
  map := 𝟙 A
  preserves := fun s i => ⟨𝟙 _, by simp⟩

/-- Composition of filtration-preserving graded maps. -/
def comp (f : FilteredMorphism F G) (g : FilteredMorphism G H) :
    FilteredMorphism F H where
  map := f.map ≫ g.map
  preserves := fun s i => by
    refine ⟨(f.preserves s i).choose ≫ (g.preserves s i).choose, ?_⟩
    change ((f.preserves s i).choose ≫ (g.preserves s i).choose) ≫
      (H.F s i).arrow = (F.F s i).arrow ≫ (f.map i ≫ g.map i)
    rw [Category.assoc, (g.preserves s i).choose_spec, ← Category.assoc,
      (f.preserves s i).choose_spec]
    simp only [Category.assoc]

lemma id_preserves_eq (F : Filtration A) (s : ℤ) (i : ι) :
    ((FilteredMorphism.id F).preserves s i).choose = 𝟙 _ := by
  apply (cancel_mono (F.F s i).arrow).mp
  rw [(FilteredMorphism.id F).preserves s i |>.choose_spec]
  dsimp [FilteredMorphism.id]
  simp

lemma comp_preserves_eq (f : FilteredMorphism F G) (g : FilteredMorphism G H)
    (s : ℤ) (i : ι) :
    ((FilteredMorphism.comp f g).preserves s i).choose =
      (f.preserves s i).choose ≫ (g.preserves s i).choose := by
  apply (cancel_mono (H.F s i).arrow).mp
  calc
    ((FilteredMorphism.comp f g).preserves s i).choose ≫
          (H.F s i).arrow =
        (F.F s i).arrow ≫ (FilteredMorphism.comp f g).map i :=
      (FilteredMorphism.comp f g).preserves s i |>.choose_spec
    _ = ((F.F s i).arrow ≫ f.map i) ≫ g.map i := by
      simp only [FilteredMorphism.comp,
        GradedObject.categoryOfGradedObjects_comp]
      simp only [Category.assoc]
    _ = ((f.preserves s i).choose ≫ (G.F s i).arrow) ≫ g.map i := by
      rw [(f.preserves s i).choose_spec]
    _ = (f.preserves s i).choose ≫
          ((G.F s i).arrow ≫ g.map i) := by simp only [Category.assoc]
    _ = (f.preserves s i).choose ≫
          ((g.preserves s i).choose ≫ (H.F s i).arrow) := by
      rw [(g.preserves s i).choose_spec]
    _ = ((f.preserves s i).choose ≫ (g.preserves s i).choose) ≫
          (H.F s i).arrow := by simp only [Category.assoc]

/-- The map on associated graded pieces induced by a filtration-preserving
morphism. -/
noncomputable def associatedGradedMap [Abelian C] (f : FilteredMorphism F G) (s : ℤ) (i : ι) :
    F.associatedGraded s i ⟶ G.associatedGraded s i :=
  cokernel.map
    (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.decreasing s i))
    (Subobject.ofLE (G.F (s + 1) i) (G.F s i) (G.decreasing s i))
    (f.preserves (s + 1) i).choose
    (f.preserves s i).choose
    (by
      apply (cancel_mono ((G.F s i).arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(f.preserves s i).choose_spec, (f.preserves (s + 1) i).choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

end FilteredMorphism

end KIP126.Core.Algebra
