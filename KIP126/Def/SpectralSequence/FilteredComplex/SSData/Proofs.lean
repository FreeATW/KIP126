import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Predicates
import KIP126.Def.SpectralSequence.FilteredPage.Proofs

/-!
# Proofs for the historical filtered-complex API
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- Convert historical boundedness to KIP126's canonical filtration predicate. -/
def IsBounded.toAlgebra {FC : FilteredComplex C} (bnd : FC.IsBounded) :
    FC.filtration.IsBounded where
  lower := bnd.lo
  upper := bnd.hi
  eq_top_of_le := bnd.boundedBelow
  eq_bot_of_le := bnd.boundedAbove
  lower_le_upper := bnd.lo_le_hi

/-- Convert canonical boundedness to the historical record. -/
def _root_.KIP126.Core.SpectralSequence.FilteredComplex.IsBounded.ofAlgebra
    {FC : FilteredComplex C}
    (bnd : FC.filtration.IsBounded) : FC.IsBounded where
  lo := bnd.lower
  hi := bnd.upper
  lo_le_hi := bnd.lower_le_upper
  boundedBelow := bnd.eq_top_of_le
  boundedAbove := bnd.eq_bot_of_le

@[simp]
theorem IsBounded.ofAlgebra_toAlgebra {FC : FilteredComplex C}
    (bnd : FC.filtration.IsBounded) :
    (FilteredComplex.IsBounded.ofAlgebra bnd).toAlgebra = bnd := by
  cases bnd
  rfl

@[simp]
theorem IsBounded.toAlgebra_ofAlgebra {FC : FilteredComplex C}
    (bnd : FC.IsBounded) :
    FilteredComplex.IsBounded.ofAlgebra bnd.toAlgebra = bnd := by
  cases bnd
  rfl

/-- Historical square-zero statement for the one-index differential. -/
theorem d_comp_d (FC : FilteredComplex C) (k : ℤ) :
    FC.d k ≫ FC.d (k - 1) = 0 := by
  change FC.complex.d k (k - 1) ≫
    FC.complex.d (k - 1) ((k - 1) - 1) = 0
  exact FC.complex.d_comp_d k (k - 1) ((k - 1) - 1)

/-- Naturality of the chain differential under transport of its target index. -/
theorem complex_d_comp_eqToHom (FC : FilteredComplex C)
    (i : ℤ) {j j' : ℤ} (h : j = j') :
    FC.complex.d i j ≫ eqToHom (congrArg FC.complex.X h) =
      FC.complex.d i j' := by
  subst j'
  simp

/-- Historical successor antitonicity statement for the filtration. -/
theorem fil_anti (FC : FilteredComplex C) (s k : ℤ) :
    FC.fil (s + 1) k ≤ FC.fil s k :=
  FC.filtration.decreasing s k

/-- Historical filtration-preservation witness. -/
theorem d_preserves_fil (FC : FilteredComplex C) (s k : ℤ) :
    ∃ φ : Subobject.underlying.obj (FC.fil s k) ⟶
        Subobject.underlying.obj (FC.fil s (k - 1)),
      φ ≫ (FC.fil s (k - 1)).arrow = (FC.fil s k).arrow ≫ FC.d k :=
  FC.differential_preserves s k

/-- Compatibility of the associated-graded differential with the quotient maps. -/
theorem assocGradedDiff_compat (FC : FilteredComplex C) (s k : ℤ) :
    FC.filToAssocGraded s k ≫ FC.assocGradedDiff s k =
      FC.filDiff s k ≫ FC.filToAssocGraded s (k - 1) :=
  FC.toAssociatedGraded_comp_associatedGradedDifferential s k

/-- Transport the associated-graded differential along equality of degrees. -/
theorem assocGradedDiff_cast (FC : FilteredComplex C)
    (s : ℤ) {k₁ k₂ : ℤ} (hk : k₁ = k₂) :
    FC.assocGradedDiff s k₁ =
      eqToHom (by rw [hk]) ≫ FC.assocGradedDiff s k₂ ≫ eqToHom (by rw [hk]) := by
  subst hk
  simp

/-- The associated-graded differential squares to zero. -/
theorem assocGradedDiff_sq (FC : FilteredComplex C) (s k : ℤ) :
    FC.assocGradedDiff s k ≫ FC.assocGradedDiff s (k - 1) = 0 :=
  FC.associatedGradedDifferential_sq s k

/-- Antitonicity between arbitrary filtration indices. -/
theorem fil_anti_of_le (FC : FilteredComplex C) {a b : ℤ} (k : ℤ)
    (hab : a ≤ b) : FC.fil b k ≤ FC.fil a k :=
  FC.filtration.le_of_le hab k

/-- Two lifts of the same associated-graded element differ through the next
filtration level.  This discharges the corresponding historical placeholder. -/
theorem isLift_sub_factors (FC : FilteredComplex C) {T : C}
    (s k : ℤ) {xl1 xl2 : T ⟶ Subobject.underlying.obj (FC.fil s k)}
    {x : T ⟶ FC.assocGraded s k}
    (h₁ : FC.IsLift s k xl1 x) (h₂ : FC.IsLift s k xl2 x) :
    Subobject.Factors (FC.fil (s + 1) k)
      ((xl1 - xl2) ≫ (FC.fil s k).arrow) := by
  let ι := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
  have hzero : (xl1 - xl2) ≫ FC.filToAssocGraded s k = 0 := by
    rw [Preadditive.sub_comp, h₁, h₂, sub_self]
  let z := Abelian.monoLift ι (xl1 - xl2) hzero
  have hz : z ≫ (FC.fil (s + 1) k).arrow =
      (xl1 - xl2) ≫ (FC.fil s k).arrow := by
    calc
    z ≫ (FC.fil (s + 1) k).arrow =
        (z ≫ ι) ≫ (FC.fil s k).arrow := by
          rw [Category.assoc, Subobject.ofLE_arrow]
    _ = (xl1 - xl2) ≫ (FC.fil s k).arrow := by
      rw [Abelian.monoLift_comp]
  rw [← hz]
  exact Subobject.factors_comp_arrow z

end FilteredComplex

end KIP126.Core.SpectralSequence
