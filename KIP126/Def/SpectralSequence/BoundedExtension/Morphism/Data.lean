import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs

/-!
# Historical filtered-complex morphism API

The old `FilteredComplexMorphism` is represented by KIP126's canonical
`FilteredComplex.Morphism`.  Compatibility accessors preserve the former API
without installing a second category structure on filtered complexes.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Compatibility name for KIP126's canonical filtration-preserving chain
map. -/
abbrev FilteredComplexMorphism (FC₁ FC₂ : FilteredComplex C) :=
  FilteredComplex.Morphism FC₁ FC₂

namespace FilteredComplexMorphism

/-- Historical degreewise-map accessor. -/
@[reducible] def f {FC₁ FC₂ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (k : ℤ) :
    FC₁.A k ⟶ FC₂.A k :=
  g.map.f k

/-- The map induced on an associated-graded piece. -/
noncomputable def assocGradedMap
    {FC₁ FC₂ : FilteredComplex C} (g : FilteredComplexMorphism FC₁ FC₂)
    (s k : ℤ) : FC₁.assocGraded s k ⟶ FC₂.assocGraded s k :=
  g.associatedGradedMap s k

end FilteredComplexMorphism

end KIP126.Core.SpectralSequence
