import KIP126.Def.SpectralSequence.BoundedExtension

/-!
# Regression checks for the historical bounded-extension API
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

noncomputable example {FC₁ FC₂ : FilteredComplex C}
    (f : ∀ k, FC₁.A k ⟶ FC₂.A k)
    (comm_d : ∀ k, f k ≫ FC₂.d k = FC₁.d k ≫ f (k - 1))
    (filt_compat : ∀ s k,
      ∃ φ : Subobject.underlying.obj (FC₁.fil s k) ⟶
          Subobject.underlying.obj (FC₂.fil s k),
        φ ≫ (FC₂.fil s k).arrow = (FC₁.fil s k).arrow ≫ f k) :
    FilteredComplexMorphism FC₁ FC₂ :=
  FilteredComplexMorphism.mk f comm_d filt_compat

noncomputable example {FC₁ FC₂ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (k : ℤ) :
    g.f k ≫ FC₂.d k = FC₁.d k ≫ g.f (k - 1) :=
  g.comm_d k

noncomputable example {FC₁ FC₂ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (s k : ℤ) :
    FC₁.assocGraded s k ⟶ FC₂.assocGraded s k :=
  g.assocGradedMap s k

example (X Y : BoundedFilteredComplex C) : Type _ := X ⟶ Y

#print axioms underlyingComplexBounded
#print axioms BoundedExtensionSS.d0_eq_inducedAssocGradedMap
#print axioms ThreeSpectraChain.boundedEssF
#print axioms FilteredComplexMorphism.comm_d
#print axioms selfComplex

end KIP126.Core.SpectralSequence
