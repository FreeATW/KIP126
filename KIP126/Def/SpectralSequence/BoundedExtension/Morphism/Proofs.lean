import KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Data

/-!
# Properties of the historical filtered-complex morphism API
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplexMorphism

/-- Historical chain-map compatibility accessor. -/
theorem comm_d {FC₁ FC₂ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (k : ℤ) :
    g.f k ≫ FC₂.d k = FC₁.d k ≫ g.f (k - 1) :=
  g.map.comm k (k - 1)

/-- Historical filtration-compatibility accessor. -/
theorem filt_compat {FC₁ FC₂ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (s k : ℤ) :
    ∃ φ : Subobject.underlying.obj (FC₁.fil s k) ⟶
        Subobject.underlying.obj (FC₂.fil s k),
      φ ≫ (FC₂.fil s k).arrow = (FC₁.fil s k).arrow ≫ g.f k :=
  g.preserves s k

/-- Reindex a historical one-index chain-map equation to an explicitly
specified target degree. -/
theorem comm_d_transport {FC₁ FC₂ : FilteredComplex C}
    (f : ∀ k, FC₁.A k ⟶ FC₂.A k)
    (comm_d : ∀ k, f k ≫ FC₂.d k = FC₁.d k ≫ f (k - 1))
    {a b : ℤ} (h : a - 1 = b) :
    f a ≫ FC₂.complex.d a b = FC₁.complex.d a b ≫ f b := by
  subst b
  exact comm_d a

/-- Historical extensionality theorem: the degreewise maps determine a
filtered-complex morphism. -/
theorem ext {FC₁ FC₂ : FilteredComplex C}
    {g h : FilteredComplexMorphism FC₁ FC₂} (e : g.f = h.f) : g = h := by
  apply FilteredComplex.Morphism.ext
  apply HomologicalComplex.Hom.ext
  exact e

end FilteredComplexMorphism

end KIP126.Core.SpectralSequence
