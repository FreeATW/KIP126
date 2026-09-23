import KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Construction.Data

/-!
# Properties of the historical morphism constructor
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplexMorphism

/-- The compatibility constructor exposes the supplied degreewise maps. -/
@[simp]
theorem mk_f {FC₁ FC₂ : FilteredComplex C}
    (f : ∀ k, FC₁.A k ⟶ FC₂.A k)
    (comm_d : ∀ k, f k ≫ FC₂.d k = FC₁.d k ≫ f (k - 1))
    (filt_compat : ∀ s k,
      ∃ φ : Subobject.underlying.obj (FC₁.fil s k) ⟶
          Subobject.underlying.obj (FC₂.fil s k),
        φ ≫ (FC₂.fil s k).arrow = (FC₁.fil s k).arrow ≫ f k)
    (k : ℤ) :
    (FilteredComplexMorphism.mk f comm_d filt_compat).f k = f k := by
  rfl

end FilteredComplexMorphism

end KIP126.Core.SpectralSequence
