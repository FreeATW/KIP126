import KIP126.Def.Synthetic.Sphere.Data

/-! Regression checks for synthetic spheres and λ-action. -/
namespace KIP126.Checks.Synthetic

open CategoryTheory
open KIP126.Synthetic.Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

example (m n : ℤ) :
    Smn (Syn := Syn) m n =
      (SyntheticCategory.biShift (m, n)).obj (S00 (Syn := Syn)) := rfl

example (m n : ℤ) (X : Syn) :
    BiHom (Syn := Syn) m n X = (Smn (Syn := Syn) m n ⟶ X) := rfl

example (m n : ℤ) (X : Syn) :
    lambdaAction (Syn := Syn) m n X = lambdaAction (Syn := Syn) m n X := rfl

example (m n k l : ℤ) (X : Syn) :
    (susp_invariance (Syn := Syn) m n k l X).toFun =
      (susp_invariance (Syn := Syn) m n k l X).toFun := rfl

end KIP126.Checks.Synthetic
