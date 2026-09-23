import KIP126.Def.Synthetic.Context.Proofs

/-! Regression checks for the explicit synthetic context interfaces. -/
namespace KIP126.Checks.Synthetic

open CategoryTheory
open KIP126.Synthetic.Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [KIP126.StableHomotopy.HasFunctorialCofiber (C := Syn)]

example (X : Syn) :
    lambdaPow 0 X = SyntheticCategory.biShift_zero.hom.app X := by
  rfl

example (X : Syn) :
    SyntheticCategory.lam.app X ≫ XModLambda.incl X = 0 :=
  XModLambda.lam_comp_incl X

example (X : Syn) (n : ℕ) :
    XModLambdaN X n =
      KIP126.StableHomotopy.HasFunctorialCofiber.cofib (lambdaPow n X) := by
  rfl

end KIP126.Checks.Synthetic
