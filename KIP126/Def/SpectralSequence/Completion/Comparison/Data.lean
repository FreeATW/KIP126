import KIP126.Def.SpectralSequence.Completion.CompletedFiltration.Data

/-!
# Comparison data for the completed filtration

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]


noncomputable def Filtration.completionψ {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s₀ : ℤ) :
    (fil.completionFiltration hbb).truncatedObj s₀ k ⟶ fil.truncatedObj (s₀ + 1) k :=
  cokernel.desc
    ((kernelSubobject (fil.completionProj' hbb k (s₀ + 1))).arrow)
    (fil.completionProj' hbb k (s₀ + 1))
    (kernelSubobject_arrow_comp _)

set_option maxHeartbeats 8000000 in
noncomputable def Filtration.completionConeLeg {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (T : C)
    (f : ∀ s₀ : ℤ, T ⟶ (fil.completionFiltration hbb).truncatedObj s₀ k) (n : ℕᵒᵖ) :
    T ⟶ fil.truncatedObj (hbb.lo k + ↑n.unop) k := by
  let s := hbb.lo k + ↑n.unop
  have step1 : T ⟶ (fil.completionFiltration hbb).truncatedObj s k := f s
  have step2 : (fil.completionFiltration hbb).truncatedObj s k ⟶ fil.truncatedObj (s + 1) k :=
    fil.completionψ hbb k s
  have step3 : fil.truncatedObj (s + 1) k ⟶ fil.truncatedObj s k :=
    fil.truncationTransition (show s ≤ s + 1 by omega) k
  exact step1 ≫ step2 ≫ step3

end KIP126.Core.SpectralSequence
