import KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Construction.Proofs
import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Predicates

/-!
# Bounded filtered complexes
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtered complex packaged with the historical two-sided boundedness
witness. -/
structure BoundedFilteredComplex
    (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The underlying filtered complex. -/
  FC : FilteredComplex C
  /-- Its filtration is bounded in every chain degree. -/
  bnd : FC.IsBounded

/-- Bounded filtered complexes form the full subcategory of filtered
complexes on bounded objects. -/
noncomputable instance : Category (BoundedFilteredComplex C) where
  Hom X Y := FilteredComplexMorphism X.FC Y.FC
  id X := FilteredComplex.Morphism.id X.FC
  comp f g := FilteredComplex.Morphism.comp f g
  id_comp f := by
    apply FilteredComplex.Morphism.ext
    simp [FilteredComplex.Morphism.comp, FilteredComplex.Morphism.id]
  comp_id f := by
    apply FilteredComplex.Morphism.ext
    simp [FilteredComplex.Morphism.comp, FilteredComplex.Morphism.id]
  assoc f g h := by
    apply FilteredComplex.Morphism.ext
    simp [FilteredComplex.Morphism.comp]

end KIP126.Core.SpectralSequence
