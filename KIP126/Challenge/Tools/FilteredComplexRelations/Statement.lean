import KIP126.Def.Algebra.Filtration.Proofs
import KIP126.Def.SpectralSequence.FilteredComplex.Data
import KIP126.Def.SpectralSequence.FilteredPage.Data
import KIP126.Def.PageExtensions.Differential.Proofs

/-!
# Open filtered-complex/page relation statements

The historical filtered-complex file contains four important relation lemmas,
but their proof bodies are still placeholders.  KIP126 keeps the canonical
Mathlib `ChainComplex`/filtration definitions and exposes the missing page
construction through an explicit `PageView` adapter.  These definitions state
the four obligations without importing the historical source or treating its
placeholder proofs as theorems.
-/

namespace KIP126.Challenge.Tools.FilteredComplexRelations

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence
open KIP126.Def.PageExtensions

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A page-level view of the canonical associated graded pieces of a filtered
complex.  The page construction and its comparison isomorphisms are exactly
the data that a future `toSpectralSequence` proof must provide. -/
structure PageView (FC : FilteredComplex C) where
  shape : ℤ → ComplexShape (ℤ × ℤ)
  firstPage : ℤ
  sequence : SpectralSequence C shape firstPage
  /-- The canonical finite/infinite page represented by a Mathlib page.

  Mathlib indexes pages by integers, whereas the filtered-complex
  construction indexes finite pages by `ℕ` and the limiting page by `⊤`.
  This translation is explicit data; no convention is hidden in the
  statement. -/
  pageNumber : ∀ (r : ℤ), firstPage ≤ r → WithTop ℕ
  /-- Comparison with the quotient page built from the canonical cycles and
  boundaries.  This is the only page object used by the relation statements.
  In particular, a page is not identified with the whole associated graded
  object. -/
  pageToPage : ∀ (r : ℤ) (hr : firstPage ≤ r) (s k : ℤ),
    (sequence.page r hr).X (s, k) ≅
      FC.pageObj s k (pageNumber r hr)

namespace PageView

variable {FC : FilteredComplex C} (P : PageView FC)

abbrev element (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ) (T : C) :=
  T ⟶ (P.sequence.page r hr).X (s, k)

def target (r s k : ℤ) : ℤ × ℤ := (s + r, k - 1)

/-- The canonical filtration differential supplied by `FilteredComplex`. -/
noncomputable def filDiff (s k : ℤ) :
    Subobject.underlying.obj (FC.filtration.F s k) ⟶
      Subobject.underlying.obj (FC.filtration.F s (k - 1)) :=
  (FC.differential_preserves s k).choose

/-- The canonical inclusion from `F^(s+r)` to `F^s`, when `r ≥ 0`. -/
noncomputable def drop (r s k : ℤ) (hr : 0 ≤ r) :
    Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1)) ⟶
      Subobject.underlying.obj (FC.filtration.F s (k - 1)) :=
  FC.filtration.inclusion (by omega) (k - 1)

/-- A lift is compared with a page element by factoring its associated-graded
image through the canonical cycle subobject and then applying `pageπ`. -/
def IsLift (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ)
    {T : C}
    (xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
    (x : P.element r hr s k T) : Prop :=
  ∃ z : T ⟶ Subobject.underlying.obj
      (FC.cycleSubobject s k (P.pageNumber r hr)),
    z ≫ (FC.cycleSubobject s k (P.pageNumber r hr)).arrow =
      xl ≫ FC.filtration.toAssociatedGraded s k ∧
    z ≫ FC.pageπ s k (P.pageNumber r hr) =
      x ≫ (P.pageToPage r hr s k).hom

def relation (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ)
    {T : C} (x : P.element r hr s k T)
    (y : P.element r hr (s + r) (k - 1) T) : Prop :=
  DifferentialRelation P.sequence r hr (s, k) (target r s k) x y

def datum (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ) :
    DifferentialDatum (c := P.shape) (r₀ := P.firstPage) P.sequence where
  page := r
  page_ge := hr
  source := (s, k)
  target := target r s k
  filtrationDegree := fun p => p.1

def crossed (r : ℤ) (hr : P.firstPage ≤ r) (s k : ℤ)
    {T : C} (x : P.element r hr s k T)
    (y : P.element r hr (s + r) (k - 1) T)
    (h : P.relation r hr s k x y) : Prop :=
  RelationCrossedBy (P.datum r hr s k) x y h

end PageView

/-! ### The four open obligations -/

/-- Forward realization of a page differential relation by filtered lifts. -/
def differentialRelationOfLift : Prop :=
  ∀ (FC : FilteredComplex C) (P : PageView FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C}
    {x : P.element r hrPage s k T}
    {y : P.element r hrPage (s + r) (k - 1) T}
    {xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    {yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1))},
    P.IsLift r hrPage s k xl x →
    P.IsLift r hrPage (s + r) (k - 1) yl y →
    xl ≫ PageView.filDiff (FC := FC) s k =
      yl ≫ PageView.drop (FC := FC) r s k hrZero →
    P.relation r hrPage s k x y

/-- Reverse realization of a page relation, with projectivity for the source
object so the page witnesses can be lifted to the filtered complex. -/
def liftOfDifferentialRelation : Prop :=
  ∀ (FC : FilteredComplex C) (P : PageView FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C} [Projective T]
    {x : P.element r hrPage s k T}
    {y : P.element r hrPage (s + r) (k - 1) T},
    P.relation r hrPage s k x y →
    ∃ (xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
      (yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1))),
      P.IsLift r hrPage s k xl x ∧
      P.IsLift r hrPage (s + r) (k - 1) yl y ∧
      xl ≫ PageView.filDiff (FC := FC) s k =
        yl ≫ PageView.drop (FC := FC) r s k hrZero

/-- Two relations from one source force the first relation to be crossed by an
essential relation, using the canonical page-level crossing predicate. -/
def differentialRelationCrossedOfTwo : Prop :=
  ∀ (FC : FilteredComplex C) (P : PageView FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C} [Projective T]
    {x : P.element r hrPage s k T}
    {y₁ y₂ : P.element r hrPage (s + r) (k - 1) T},
    (h₁ : P.relation r hrPage s k x y₁) →
    P.relation r hrPage s k x y₂ →
    P.crossed r hrPage s k x y₁ h₁

/-- If a relation is not crossed, every compatible filtered lift realizes its
target page element. -/
def liftRelOfNotCrossed : Prop :=
  ∀ (FC : FilteredComplex C) (P : PageView FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C} [Projective T]
    {x : P.element r hrPage s k T}
    {y₁ : P.element r hrPage (s + r) (k - 1) T},
    (h₁ : P.relation r hrPage s k x y₁) →
    (hnc : ¬ P.crossed r hrPage s k x y₁ h₁) →
    {xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)} →
    P.IsLift r hrPage s k xl x →
    (yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1))) →
    xl ≫ PageView.filDiff (FC := FC) s k =
      yl ≫ PageView.drop (FC := FC) r s k hrZero →
    P.IsLift r hrPage (s + r) (k - 1) yl y₁

end KIP126.Challenge.Tools.FilteredComplexRelations
