import KIP126.Def.SpectralSequence.Convergence.SSData.Predicates

/-!
# Detection sets
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- Representatives in the target filtration detected by an infinity-page
class.  This is the historical `DetectionSet` API. -/
def DetectionSet
    {E : SpectralSequence C ω} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) {T : C} (k : ω)
    (y : T ⟶ (E.ssData k).eInfty) :=
  { x : T ⟶ Subobject.underlying.obj
      (F.F (conv.reindex k).1 (conv.reindex k).2) //
    Detects conv y x }

end KIP126.Core.SpectralSequence
