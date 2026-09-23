import Mathlib.Algebra.Group.Hom.Defs

/-!
# The order-two `theta_5` interface

This file contains the small algebraic interface used by the near-126
choice-transport argument.  It deliberately does not manufacture a synthetic
homotopy class.  A concrete formalisation supplies the carrier, the square,
the `lambda eta` map, and the finite quotient predicates as fields of
`Theta5ChoiceContext`.
-/

namespace KIP126.Kervaire

open KIP126

section ChoiceContext

variable {Carrier : Type} [AddCommGroup Carrier]

/-- The order-two predicate attached to one synthetic class. -/
def IsOrderTwo (θ : Carrier) : Prop := θ + θ = 0

/-- The data needed to compare two representatives detected by `h_5^2`.

`difference` is kept explicit because the eventual synthetic carrier is a
graded group and its subtraction may involve a transport across a grading
identification.  The two equations `difference_spec` and `square_difference`
are the corresponding internal coherence fields; neither is an axiom of the
project and neither selects a representative.
-/
structure Theta5ChoiceContext where
  square : Carrier → Carrier
  lambdaEta : Carrier →+ Carrier
  isChoice : Carrier → Prop
  sourceChoice : Carrier
  sourceChoice_isChoice : isChoice sourceChoice
  difference : Carrier → Carrier → Carrier
  difference_spec : ∀ θ ψ, ψ + difference θ ψ = θ
  highDifference : Carrier → Prop
  correction : Carrier → Carrier → Carrier
  square_difference : ∀ θ ψ,
    square θ = square ψ + correction θ ψ
  correction_vanishes : ∀ {θ ψ},
    highDifference (difference θ ψ) →
      lambdaEta (correction θ ψ) = 0
  finiteZero : ℕ → Carrier → Prop
  untruncatedZero : Carrier → Prop
  h6Survives : ℕ → Prop
  is_permanent : Carrier → Prop
  deltaH6 : Carrier
  /-- Finite evidence that the two comparison groups have no relevant
  `lambda`-torsion.  The concrete group interpretation supplies these
  propositions; the context does not choose a class witnessing either one. -/
  noLambdaTorsion62 : Prop
  noLambdaTorsion125 : Prop

namespace Theta5ChoiceContext

variable {Carrier : Type} [AddCommGroup Carrier]

variable (C : Theta5ChoiceContext (Carrier := Carrier))

@[simp] theorem sourceChoice_isChoice_eq : C.isChoice C.sourceChoice :=
  C.sourceChoice_isChoice

/-- The finite class used by the external BJM/BX comparison. -/
def sourceExpression : Carrier := C.lambdaEta (C.square C.sourceChoice)

end Theta5ChoiceContext

end ChoiceContext

end KIP126.Kervaire
