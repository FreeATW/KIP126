import KIP126.Def.Algebra.Coefficients.Data
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# An E₂ multiplication table and its presented algebra

This constructs a *model algebra*, not the E₂ page of a spectral sequence.
Only products whose source and target degrees are covered generate relations.
In particular, an out-of-range product is not set to zero.
-/

namespace KIP126.AdamsE2

open KIP126.Core.Algebra
open scoped BigOperators

abbrev Degree := ℤ × ℤ

/-- Semantic input format. An importer supplies dimensions and basis products;
the functions can be backed by generated arrays or sparse tables. Values of
`dim` outside `region` have no mathematical meaning. -/
structure Table where
  region : Finset Degree
  dim : Degree → ℕ
  mulCoeff : ∀ p q, p ∈ region → q ∈ region → p + q ∈ region →
    Fin (dim p) → Fin (dim q) → Fin (dim (p + q)) → F2
  zero_mem : (0, 0) ∈ region
  unitCoeff : Fin (dim (0, 0)) → F2

namespace Table

abbrev Cell (T : Table) := { p : Degree // p ∈ T.region }
abbrev Generator (T : Table) := Σ p : T.Cell, Fin (T.dim p.val)
abbrev Poly (T : Table) := MvPolynomial T.Generator F2

noncomputable section

/-- One formal symbol for each recorded additive basis element. -/
def symbol (T : Table) (p : Degree) (hp : p ∈ T.region)
    (i : Fin (T.dim p)) : T.Poly :=
  MvPolynomial.X ⟨⟨p, hp⟩, i⟩

/-- A covered table entry interpreted as a polynomial relation. -/
def mulRelation (T : Table) (p q : Degree)
    (hp : p ∈ T.region) (hq : q ∈ T.region) (hpq : p + q ∈ T.region)
    (i : Fin (T.dim p)) (j : Fin (T.dim q)) : T.Poly :=
  T.symbol p hp i * T.symbol q hq j -
    ∑ k, T.mulCoeff p q hp hq hpq i j k • T.symbol (p + q) hpq k

/-- The recorded degree-zero vector represents the multiplicative unit. -/
def unitRelation (T : Table) : T.Poly :=
  (∑ i, T.unitCoeff i • T.symbol (0, 0) T.zero_mem i) - 1

/-- There are no relations for products outside the declared coverage. -/
def relations (T : Table) : Set T.Poly :=
  { f | f = T.unitRelation ∨ ∃ p q hp hq hpq i j,
    f = T.mulRelation p q hp hq hpq i j }

def relationIdeal (T : Table) : Ideal T.Poly := Ideal.span T.relations

/-- The ring presented by the table, distinct from the actual Adams page. -/
abbrev Model (T : Table) := T.Poly ⧸ T.relationIdeal

def quotient (T : Table) : T.Poly →ₐ[F2] T.Model :=
  Ideal.Quotient.mkₐ F2 T.relationIdeal

def generator (T : Table) (p : Degree) (hp : p ∈ T.region)
    (i : Fin (T.dim p)) : T.Model :=
  T.quotient (T.symbol p hp i)

/-- The image of the weighted homogeneous polynomials in the model quotient.
This definition does not claim that the imported dimension is correct. -/
def piece (T : Table) (p : Degree) : Submodule F2 T.Model :=
  (MvPolynomial.weightedHomogeneousSubmodule F2
    (fun g : T.Generator => g.1.val) p).map T.quotient.toLinearMap

end
end Table
end KIP126.AdamsE2
