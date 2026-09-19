import KIP126.Def.Algebra.Filtration.Data

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

namespace Filtration

variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

/-- A filtration is degreewise eventually top: every component is the whole
object at some filtration level.  Because the filtration is decreasing, it is
then top at every lower level.  This predicate is stronger than ordinary
exhaustiveness expressed only by a union or colimit of filtration levels. -/
def IsExhaustive (F : Filtration A) : Prop :=
  ∀ i : ι, ∃ s : ℤ, F.F s i = ⊤

/-- A filtration is degreewise eventually bottom: every component vanishes at
some filtration level.  Because the filtration is decreasing, it then vanishes
at every higher level.  This is stronger than separatedness, which asks only
for zero intersection. -/
def IsEventuallyZero [Abelian C] (F : Filtration A) : Prop :=
  ∀ i : ι, ∃ s : ℤ, F.F s i = ⊥

/-! A Mittag-Leffler condition for the decreasing filtration.  The images of
deeper levels inside any fixed level must eventually stabilize. -/

/-- The filtration images `F^(s+n) ↪ F^s` stabilize degreewise. -/
def IsMittagLeffler [Abelian C] (F : Filtration A) : Prop :=
  ∀ (i : ι) (s : ℤ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    imageSubobject (F.inclusion (t := s) (s := s + (n : ℤ)) (by omega) i) =
      imageSubobject (F.inclusion (t := s) (s := s + (N : ℤ)) (by omega) i)

/-- A filtration is bounded below degreewise if sufficiently low levels are
the whole object. -/
structure IsBoundedBelow (F : Filtration A) where
  /-- A lower filtration bound for each graded component. -/
  lower : ι → ℤ
  eq_top_of_le : ∀ (i : ι) (s : ℤ), s ≤ lower i → F.F s i = ⊤

/-- A filtration is bounded above degreewise if sufficiently high levels are
zero. -/
structure IsBoundedAbove [Abelian C] (F : Filtration A) where
  /-- An upper filtration bound for each graded component. -/
  upper : ι → ℤ
  eq_bot_of_le : ∀ (i : ι) (s : ℤ), upper i ≤ s → F.F s i = ⊥

/-- A degreewise bounded filtration has both a lower and an upper bound. -/
structure IsBounded [Abelian C] (F : Filtration A) extends IsBoundedBelow F, IsBoundedAbove F where
  lower_le_upper : ∀ i : ι, lower i ≤ upper i

end Filtration

end KIP126.Core.Algebra
