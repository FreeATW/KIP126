import KIP126.Def.Algebra.Completion.Data
import KIP126.Def.Algebra.Filtration.Predicates

/-!
# Filtrations on canonical quotient objects

The quotient object, projection, and transition maps already belong to
`Completion.Data`. Here we port the image filtration from KIPBase's truncation
construction directly to those objects. The parameter `q` is the quotient
level itself; callers choosing the historical truncation at `s₀` pass
`q = s₀ + 1`.
-/

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

namespace Filtration

/-- The image filtration induced on a truncation. -/
noncomputable def quotientFiltration (fil : Filtration A) (q : ℤ) :
    Filtration (fun i => fil.quotientAt q i) where
  F s i := imageSubobject ((fil.F s i).arrow ≫ fil.quotientProjection q i)
  decreasing s i := by
    rw [show (fil.F (s + 1) i).arrow ≫ fil.quotientProjection q i =
      Subobject.ofLE _ _ (fil.decreasing s i) ≫
        (fil.F s i).arrow ≫ fil.quotientProjection q i
      from by rw [← Category.assoc, Subobject.ofLE_arrow]]
    exact imageSubobject_comp_le _ _

end Filtration

end KIP126.Core.Algebra
