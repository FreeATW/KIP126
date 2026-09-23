import KIP126.Def.SpectralSequence.Truncation.Proofs

/-!
# Completion tower data

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

/-- The truncation system as a functor `ℕᵒᵖ ⥤ C`: sends `n` to
    `A(k)/F^{lo(k)+n+1}(A(k))` with transition maps from `truncationTransition`. -/
noncomputable def Filtration.completionFunctor {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) :
    ℕᵒᵖ ⥤ C where
  obj n := fil.truncatedObj (hbb.lo k + ↑n.unop) k
  map {m n} f := fil.truncationTransition (by have := leOfHom f.unop; omega) k
  map_id n := by
    apply (cancel_epi (cokernel.π ((fil.F (hbb.lo k + ↑n.unop + 1) k).arrow))).mp
    erw [Category.comp_id]; exact cokernel.π_desc _ _ _
  map_comp {l m n} f g := (fil.truncationTransition_comp _ _ k).symm

noncomputable def Filtration.completion {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) : C :=
  limit (fil.completionFunctor hbb k)

/-- Projection from the completion to `truncatedObj s k` for arbitrary `s`. -/
noncomputable def Filtration.completionProj' {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) (s : ℤ) :
    fil.completion hbb k ⟶ fil.truncatedObj s k :=
  limit.π (fil.completionFunctor hbb k) (Opposite.op (s - hbb.lo k).toNat) ≫
    fil.truncationTransition (show s ≤ hbb.lo k + ↑(s - hbb.lo k).toNat by omega) k

set_option maxHeartbeats 2000000 in
/-- The canonical map `A(k) → Â(k)` to the completion. -/
noncomputable def Filtration.toCompletion {ω : Type w} {A : ω → C}
    (fil : Filtration A) (hbb : fil.IsBoundedBelow) (k : ω) :
    A k ⟶ fil.completion hbb k :=
  limit.lift (fil.completionFunctor hbb k) {
    pt := A k
    π := {
      app := fun n => by exact fil.truncationProj (hbb.lo k + ↑n.unop) k
      naturality := by
        intro m n f
        dsimp [Filtration.completionFunctor]
        calc
          𝟙 (A k) ≫ fil.truncationProj (hbb.lo k + ↑n.unop) k =
              fil.truncationProj (hbb.lo k + ↑n.unop) k := Category.id_comp _
          _ = fil.truncationProj (hbb.lo k + ↑m.unop) k ≫
                fil.truncationTransition
                  (show hbb.lo k + ↑n.unop ≤ hbb.lo k + ↑m.unop from
                    by have := leOfHom f.unop; omega) k :=
              (fil.truncationProj_transition _ k).symm
    }
  }

end KIP126.Core.SpectralSequence
