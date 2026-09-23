import KIP126.Def.SpectralSequence.Completion.Comparison.Proofs

/-!
# Universal-property lift data

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
noncomputable def Filtration.completionLift {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k)
    (hcompat : ∀ (s₀ s₁ : ℤ) (h : s₀ ≤ s₁),
      f s₁ ≫ (fil.completionFiltration hbb).truncationTransition h k = f s₀) :
    T ⟶ fil.completion hbb k :=
  limit.lift (fil.completionFunctor hbb k) {
    pt := T
    π := {
      app := fun n => fil.completionConeLeg hbb k T f n
      naturality := by
        intro m n φ
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact fil.completionConeLeg_naturality hbb k T f hcompat m n φ
    }
  }

end KIP126.Core.SpectralSequence
