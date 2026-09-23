import KIP126.Def.SpectralSequence.BoundedExtension.Morphism.Proofs

/-!
# Construction of historical filtered-complex morphisms
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplexMorphism

/-- Constructor with the argument order and one-index differential convention
of the historical API. -/
noncomputable def mk {FC₁ FC₂ : FilteredComplex C}
    (f : ∀ k, FC₁.A k ⟶ FC₂.A k)
    (comm_d : ∀ k, f k ≫ FC₂.d k = FC₁.d k ≫ f (k - 1))
    (filt_compat : ∀ s k,
      ∃ φ : Subobject.underlying.obj (FC₁.fil s k) ⟶
          Subobject.underlying.obj (FC₂.fil s k),
        φ ≫ (FC₂.fil s k).arrow = (FC₁.fil s k).arrow ≫ f k) :
    FilteredComplexMorphism FC₁ FC₂ where
  map := ChainComplex.ofHom f (fun k =>
    comm_d_transport f comm_d (by omega : k + 1 - 1 = k))
  preserves := filt_compat

end FilteredComplexMorphism

end KIP126.Core.SpectralSequence
