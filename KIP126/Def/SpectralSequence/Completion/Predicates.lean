import KIP126.Def.SpectralSequence.Completion.Data

/-!
# Completion predicates

Axiom-free migration of the corresponding historical completion layer.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C]

/-- The Mittag-Leffler condition: images of deeper filtration levels in a
    given level stabilize. -/
def Filtration.IsMittagLeffler {ω : Type w} {A : ω → C}
    (fil : Filtration A) : Prop :=
  ∀ (k : ω) (s : ℤ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
    imageSubobject (Subobject.ofLE (fil.F (s + ↑n) k) (fil.F s k)
      (fil.mono_of_le (by omega) k)) =
    imageSubobject (Subobject.ofLE (fil.F (s + ↑N) k) (fil.F s k)
      (fil.mono_of_le (by omega) k))

end KIP126.Core.SpectralSequence
