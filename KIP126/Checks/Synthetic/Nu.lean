import KIP126.Def.Synthetic.Context.Proofs

/-! Regression check for the explicit ν witness record. -/
namespace KIP126.Checks.Synthetic

open CategoryTheory
open KIP126.Synthetic.Context

universe u v u' v'

variable {Stable : Type u} [KIP126.StableHomotopy.StableHomotopyCategory.{u, v} Stable]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]

example (N : NuFunctorData Stable Syn) (X : Stable) :
    Nonempty
      (N.functor.obj ((shiftFunctor Stable (1 : ℤ)).obj X) ≅
        (SyntheticCategory.biShift (1, 1)).obj (N.functor.obj X)) :=
  ⟨N.suspensionIso X⟩

example (N : NuFunctorData Stable Syn) (n : ℤ) (X : Stable) :
    Nonempty
      (N.functor.obj ((shiftFunctor Stable n).obj X) ≅
        (SyntheticCategory.biShift (n, n)).obj (N.functor.obj X)) :=
  ⟨N.shiftBiShift n X⟩

end KIP126.Checks.Synthetic
