import KIP126.Def.SpectralSequence.Convergence.SSData.Data

/-!
# Convergence predicates for nested-subobject spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtration is bounded on both sides degreewise. -/
structure Filtration.IsBounded
    {ω : Type w} {A : ω → C} (F : Filtration A) where
  /-- Lower bound. -/
  lo : ω → ℤ
  /-- Upper bound. -/
  hi : ω → ℤ
  /-- Bounds occur in the expected order. -/
  lo_le_hi : ∀ k, lo k ≤ hi k
  /-- The filtration is top below the lower bound. -/
  boundedBelow : ∀ (k : ω) (s : ℤ), s ≤ lo k → F.F s k = ⊤
  /-- The filtration is bottom above the upper bound. -/
  boundedAbove : ∀ (k : ω) (s : ℤ), hi k ≤ s → F.F s k = ⊥

/-- A filtration is bounded below degreewise. -/
structure Filtration.IsBoundedBelow
    {ω : Type w} {A : ω → C} (F : Filtration A) where
  /-- Lower bound. -/
  lo : ω → ℤ
  /-- The filtration is top below the bound. -/
  boundedBelow : ∀ (k : ω) (s : ℤ), s ≤ lo k → F.F s k = ⊤

/-- A filtration is bounded above degreewise. -/
structure Filtration.IsBoundedAbove
    {ω : Type w} {A : ω → C} (F : Filtration A) where
  /-- Upper bound. -/
  hi : ω → ℤ
  /-- The filtration is bottom above the bound. -/
  boundedAbove : ∀ (k : ω) (s : ℤ), hi k ≤ s → F.F s k = ⊥

/-- Degreewise exhaustiveness. -/
def Filtration.IsExhaustive
    {ω : Type w} {A : ω → C} (F : Filtration A) : Prop :=
  ∀ (k : ω), ∃ (s : ℤ), F.F s k = ⊤

/-- Degreewise Hausdorffness/separatedness in the eventually-zero form. -/
def Filtration.IsHausdorff
    {ω : Type w} {A : ω → C} (F : Filtration A) : Prop :=
  ∀ (k : ω), ∃ (s : ℤ), F.F s k = ⊥

/-- The infinity-page class `y` detects the filtered class represented by `x`. -/
def Detects
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ (E.ssData k).eInfty)
    (x : T ⟶ Subobject.underlying.obj
      (F.F (conv.reindex k).1 (conv.reindex k).2)) : Prop :=
  y ≫ (conv.iso k).hom =
    x ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2

end KIP126.Core.SpectralSequence
