import KIP126.Def.SpectralSequence.FilteredComplex.Relations.Predicates

/-!
# Proofs for filtered-complex/page relations

The four relation theorems are internal proof obligations, rather than paper
milestones.  Their theorem statements are kept here directly; the unfinished
proof bodies are explicit `by sorry` placeholders.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory
open KIP126.Core.Algebra

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace PageView

variable {FC : FilteredComplex C} (P : PageView FC)

/-- Two lifts of one page element differ by a map through the page boundary. -/
theorem isLift_sub_factors_boundary
    {r : ℤ} {hr : P.firstPage ≤ r} {s k : ℤ} {T : C}
    {x : P.element r hr s k T}
    {xl₁ xl₂ : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    (h₁ : P.IsLift r hr s k xl₁ x)
    (h₂ : P.IsLift r hr s k xl₂ x) :
    (FC.boundarySubobject s k (P.pageNumber r hr)).Factors
      ((xl₁ - xl₂) ≫ FC.filtration.toAssociatedGraded s k) := by
  rcases h₁ with ⟨z₁, hz₁, hp₁⟩
  rcases h₂ with ⟨z₂, hz₂, hp₂⟩
  let B := FC.boundarySubobject s k (P.pageNumber r hr)
  let Z := FC.cycleSubobject s k (P.pageNumber r hr)
  let hBZ := FC.B_le_Z_aux s k (P.pageNumber r hr)
  let ι := Subobject.ofLE B Z hBZ
  have hpage : (z₁ - z₂) ≫ FC.pageπ s k (P.pageNumber r hr) = 0 := by
    rw [Preadditive.sub_comp, hp₁, hp₂, sub_self]
  let w : T ⟶ Subobject.underlying.obj B :=
    Abelian.monoLift ι (z₁ - z₂) hpage
  have hw : w ≫ ι = z₁ - z₂ :=
    Abelian.monoLift_comp ι (z₁ - z₂) hpage
  have hdiff :
      (xl₁ - xl₂) ≫ FC.filtration.toAssociatedGraded s k =
        w ≫ B.arrow := by
    calc
      (xl₁ - xl₂) ≫ FC.filtration.toAssociatedGraded s k =
          (xl₁ ≫ FC.filtration.toAssociatedGraded s k) -
            (xl₂ ≫ FC.filtration.toAssociatedGraded s k) := by
              rw [Preadditive.sub_comp]
      _ = (z₁ ≫ Z.arrow) - (z₂ ≫ Z.arrow) := by rw [← hz₁, ← hz₂]
      _ = (z₁ - z₂) ≫ Z.arrow := by rw [← Preadditive.sub_comp]
      _ = w ≫ ι ≫ Z.arrow := by rw [← hw, Category.assoc]
      _ = w ≫ B.arrow := by rw [Subobject.ofLE_arrow hBZ]
  rw [hdiff]
  exact Subobject.factors_comp_arrow w

end PageView

/-! The following four declarations are internal relation lemmas, not
challenge milestones. -/

theorem differentialRelationOfLift
    (FC : FilteredComplex C) (P : PageView FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C}
    {x : P.element r hrPage s k T}
    {y : P.element r hrPage (s + r) (k - 1) T}
    {xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    {yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1))}
    (hxl : P.IsLift r hrPage s k xl x)
    (hyl : P.IsLift r hrPage (s + r) (k - 1) yl y)
    (hd : xl ≫ PageView.filDiff (FC := FC) s k =
      yl ≫ PageView.drop (FC := FC) r s k hrZero) :
    P.relation r hrPage s k x y := by
  sorry

theorem liftOfDifferentialRelation
    (FC : FilteredComplex C) (P : PageView FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C} [Projective T]
    {x : P.element r hrPage s k T}
    {y : P.element r hrPage (s + r) (k - 1) T}
    (hrel : P.relation r hrPage s k x y) :
    ∃ (xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
      (yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1))),
      P.IsLift r hrPage s k xl x ∧
      P.IsLift r hrPage (s + r) (k - 1) yl y ∧
      xl ≫ PageView.filDiff (FC := FC) s k =
        yl ≫ PageView.drop (FC := FC) r s k hrZero := by
  sorry

theorem differentialRelationCrossedOfTwo
    (FC : FilteredComplex C) (P : PageView FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C} [Projective T]
    {x : P.element r hrPage s k T}
    {y₁ y₂ : P.element r hrPage (s + r) (k - 1) T}
    (h₁ : P.relation r hrPage s k x y₁)
    (h₂ : P.relation r hrPage s k x y₂) :
    P.crossed r hrPage s k x y₁ h₁ := by
  sorry

theorem liftRelOfNotCrossed
    (FC : FilteredComplex C) (P : PageView FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C} [Projective T]
    {x : P.element r hrPage s k T}
    {y₁ : P.element r hrPage (s + r) (k - 1) T}
    (h₁ : P.relation r hrPage s k x y₁)
    (hnc : ¬ P.crossed r hrPage s k x y₁ h₁)
    {xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    (hxl : P.IsLift r hrPage s k xl x)
    (yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1)))
    (hd : xl ≫ PageView.filDiff (FC := FC) s k =
      yl ≫ PageView.drop (FC := FC) r s k hrZero) :
    P.IsLift r hrPage (s + r) (k - 1) yl y₁ := by
  sorry

end KIP126.Core.SpectralSequence.FilteredComplex
