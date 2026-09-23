import KIP126.Def.Synthetic.Context.Data

/-! Derived distinguished-triangle facts for synthetic λ-quotients. -/
namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy

universe u v u' v'

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Iterated suspension compatibility for an explicit ν witness. -/
noncomputable def NuFunctorData.shiftBiShift
    {Stable : Type u} [StableHomotopyCategory.{u, v} Stable]
    {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
    (N : NuFunctorData Stable Syn) (n : ℤ) (X : Stable) :
    N.functor.obj ((shiftFunctor Stable n).obj X) ≅
      (SyntheticCategory.biShift (n, n)).obj (N.functor.obj X) :=
  Int.inductionOn' n 0
    (N.functor.mapIso ((shiftFunctorZero Stable ℤ).app X) ≪≫
      SyntheticCategory.biShift_zero.symm.app (N.functor.obj X))
    (fun k _hk ih => by
      have step1 := N.functor.mapIso ((shiftFunctorAdd Stable k 1).app X)
      have step2 := N.suspensionIso ((shiftFunctor Stable k).obj X)
      have step3 := (SyntheticCategory.biShift (1, 1)).mapIso ih
      have step4 :
          (SyntheticCategory.biShift (1, 1)).obj
              ((SyntheticCategory.biShift (k, k)).obj (N.functor.obj X)) ≅
            (SyntheticCategory.biShift (k + 1, k + 1)).obj (N.functor.obj X) :=
        (SyntheticCategory.biShift_comp (k, k) (1, 1)).app
            (N.functor.obj X) ≪≫ eqToIso (by simp)
      exact step1 ≪≫ step2 ≪≫ step3 ≪≫ step4)
    (fun k _hk ih => by
      set Y := (shiftFunctor Stable (k - 1)).obj X
      have chain1 := N.suspensionIso Y
      have chain2 :
          N.functor.obj ((shiftFunctor Stable (1 : ℤ)).obj Y) ≅
            N.functor.obj ((shiftFunctor Stable k).obj X) :=
        N.functor.mapIso ((shiftFunctorAdd Stable (k - 1) 1).symm.app X ≪≫
          eqToIso (by simp))
      have combined :
          (SyntheticCategory.biShift (1, 1)).obj (N.functor.obj Y) ≅
            (SyntheticCategory.biShift (k, k)).obj (N.functor.obj X) :=
        chain1.symm ≪≫ chain2 ≪≫ ih
      have cancel := (SyntheticCategory.biShift (-1, -1)).mapIso combined
      have lhs_simp :
          (SyntheticCategory.biShift (-1, -1)).obj
              ((SyntheticCategory.biShift (1, 1)).obj (N.functor.obj Y)) ≅
            N.functor.obj Y :=
        (SyntheticCategory.biShift_comp (1, 1) (-1, -1)).app
            (N.functor.obj Y) ≪≫ eqToIso (by simp) ≪≫
          SyntheticCategory.biShift_zero.app (N.functor.obj Y)
      have rhs_simp :
          (SyntheticCategory.biShift (-1, -1)).obj
              ((SyntheticCategory.biShift (k, k)).obj (N.functor.obj X)) ≅
            (SyntheticCategory.biShift (k - 1, k - 1)).obj (N.functor.obj X) :=
        (SyntheticCategory.biShift_comp (k, k) (-1, -1)).app
            (N.functor.obj X) ≪≫ eqToIso (by simp [sub_eq_add_neg])
      exact lhs_simp.symm ≪≫ cancel ≪≫ rhs_simp)

/-- The inclusion into the cofiber of `λ_X`. -/
noncomputable def XModLambda.incl (X : Syn) :
    X ⟶ XModLambda X :=
  HasFunctorialCofiber.cofibι (SyntheticCategory.lam.app X)

/-- The connecting map out of the cofiber of `λ_X`. -/
noncomputable def XModLambda.proj (X : Syn) :
    XModLambda X ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -1)).obj X) :=
  HasFunctorialCofiber.cofibδ (SyntheticCategory.lam.app X)

/-- The λ cofiber triangle is distinguished. -/
theorem XModLambda.triangle_distinguished (X : Syn) :
    Triangle.mk (SyntheticCategory.lam.app X)
      (XModLambda.incl X) (XModLambda.proj X) ∈ distTriang Syn :=
  HasFunctorialCofiber.cofib_distinguished (SyntheticCategory.lam.app X)

@[simp] theorem XModLambda.lam_comp_incl (X : Syn) :
    SyntheticCategory.lam.app X ≫ XModLambda.incl X = 0 :=
  comp_distTriang_mor_zero₁₂ _ (XModLambda.triangle_distinguished X)

/-- The λⁿ cofiber triangle is distinguished. -/
theorem XModLambdaN.triangle_distinguished (X : Syn) (n : ℕ) :
    Triangle.mk (lambdaPow n X)
      (HasFunctorialCofiber.cofibι (lambdaPow n X))
      (HasFunctorialCofiber.cofibδ (lambdaPow n X)) ∈ distTriang Syn :=
  HasFunctorialCofiber.cofib_distinguished (lambdaPow n X)

end KIP126.Synthetic.Context
