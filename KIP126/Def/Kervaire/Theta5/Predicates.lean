import KIP126.Def.Kervaire.Theta5.Data

/-!
# Predicates for the `theta_5` external boundary

The propositions in this file are interfaces.  Their proofs are supplied by a
located literature result or a checked finite computation; the definitions do
not assert any of the Kervaire conclusions themselves.
-/

namespace KIP126.Kervaire

section Statements

variable {Carrier : Type} [AddCommGroup Carrier]
variable (C : Theta5ChoiceContext (Carrier := Carrier))

/-- The Xu/IWX order and choice-filtration input used by the project proof. -/
def Theta5OrderData : Prop :=
  (∀ θ, C.isChoice θ → IsOrderTwo θ) ∧
    (∀ θ ψ, C.isChoice θ → C.isChoice ψ →
      C.highDifference (C.difference θ ψ))

/-- The source-specific BJM/BX criterion.  This proposition is deliberately
quantified only at the distinguished source choice; the project transport
theorem in `Proofs.lean` supplies the arbitrary-choice form. -/
def BJM_BXCriterion : Prop :=
  IsOrderTwo C.sourceChoice ∧
    (∀ r : ℕ, 1 ≤ r →
      (C.h6Survives (r + 3) ↔
        C.finiteZero (r + 1) C.sourceExpression)) ∧
    (C.is_permanent C.sourceExpression ↔ C.untruncatedZero C.sourceExpression)

/-- The located total-differential identity for every order-two choice. -/
def TotalDifferentialIdentity : Prop :=
  ∀ θ, C.isChoice θ → IsOrderTwo θ →
    C.deltaH6 = C.lambdaEta (C.square θ)

/-- The finite torsion/filtration evidence consumed by the near-126 layer.
The first clause records order two and the second records the filtration bound
on a difference of choices. -/
def Theta5OrderTorsionEvidence : Prop :=
  Theta5OrderData C ∧ C.noLambdaTorsion62 ∧ C.noLambdaTorsion125

/-- Browder's geometric criterion, parameterized by one fixed framed context.
The existential side is the dimension-indexed statement used by the endpoint
theorems; the Adams permanence predicate is supplied by the same fixed sphere
sequence. -/
def BrowderCriterionStatement
    {Manifold : Type}
    (dimension : Manifold → ℕ)
    (kervaireOne : Manifold → Prop)
    (permanent : ℕ → Prop) : Prop :=
  ∀ n : ℕ,
    ((∃ M, dimension M = n ∧ kervaireOne M) ↔
      ∃ j : ℕ, 1 ≤ j ∧ n = 2 ^ (j + 1) - 2 ∧ permanent j)

/-- The HHR nonexistence result, with the project's framed-manifold predicate
and dimension convention as explicit parameters. -/
def HHRNonexistenceStatement
    {Manifold : Type}
    (dimension : Manifold → ℕ)
    (kervaireOne : Manifold → Prop) : Prop :=
  ∀ j : ℕ, 7 ≤ j →
    ¬ ∃ M, dimension M = 2 ^ (j + 1) - 2 ∧ kervaireOne M

/-- The Barratt--Jones--Mahowald inductive input. -/
def BJMInductionStatement
    {Class : Type}
    (detected : ℕ → Class → Prop)
    (isOrderTwo : Class → Prop)
    (squareZero : Class → Prop) : Prop :=
  ∀ j : ℕ, ∀ θ : Class,
    detected j θ → isOrderTwo θ → squareZero θ →
      ∃ next : Class, detected (j + 1) next ∧ isOrderTwo next

end Statements

end KIP126.Kervaire
