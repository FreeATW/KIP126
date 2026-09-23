import Mathlib.Algebra.Homology.SpectralSequence.Basic
import KIP126.Def.SpectralSequence.FilteredDifferential.Proofs

/-!
# Finite quotient pages as Mathlib homological complexes

The canonical quotient page and its filtered differential determine a Mathlib
`HomologicalComplex` at every finite page.  The adjacent-page homology
isomorphism and final spectral-sequence assembly are proved separately.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The bidegree shape of the finite `n`th page. -/
def pageShape (n : ℕ) : ComplexShape (ℤ × ℤ) :=
  ComplexShape.up' ((n : ℤ), (-1 : ℤ))

/-- The differential on a finite quotient page, extended by zero off the page shape. -/
noncomputable def pageDifferentialHom (FC : FilteredComplex C) (n : ℕ)
    (p q : ℤ × ℤ) :
    FC.pageObj p.1 p.2 (n : WithTop ℕ) ⟶ FC.pageObj q.1 q.2 (n : WithTop ℕ) := by
  by_cases hpq : (pageShape n).Rel p q
  · change p + ((n : ℤ), (-1 : ℤ)) = q at hpq
    refine FC.pageDifferential p.1 p.2 n ≫ eqToHom ?_
    rw [← hpq]
    rfl
  · exact 0

@[simp]
lemma pageDifferentialHom_of_rel (FC : FilteredComplex C) (n : ℕ)
    (p q : ℤ × ℤ) (hpq : (pageShape n).Rel p q) :
    FC.pageDifferentialHom n p q =
      FC.pageDifferential p.1 p.2 n ≫ eqToHom (by
        rw [← hpq]
        rfl) := by
  dsimp [pageDifferentialHom]
  rw [dif_pos hpq]

/-- The finite page as a Mathlib homological complex. -/
noncomputable def pageComplex (FC : FilteredComplex C) (n : ℕ) :
    HomologicalComplex C (pageShape n) where
  X p := FC.pageObj p.1 p.2 (n : WithTop ℕ)
  d p q := FC.pageDifferentialHom n p q
  shape p q hpq := by
    dsimp [pageDifferentialHom]
    rw [dif_neg hpq]
  d_comp_d' p q r hpq hqr := by
    rcases p with ⟨s, k⟩
    rcases q with ⟨s1, k1⟩
    rcases r with ⟨s2, k2⟩
    dsimp [pageDifferentialHom, pageShape, ComplexShape.up'] at hpq hqr ⊢
    rw [dif_pos hpq, dif_pos hqr]
    rcases hpq with ⟨rfl, rfl⟩
    rcases hqr with ⟨rfl, rfl⟩
    convert FC.pageDifferential_comp s k n using 1 <;>
      simp [Int.sub_eq_add_neg]
    all_goals rfl

end KIP126.Core.SpectralSequence.FilteredComplex
