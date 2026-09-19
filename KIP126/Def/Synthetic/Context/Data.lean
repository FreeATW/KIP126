import KIP126.Def.StableHomotopy.Context.Data

/-!
# Bigraded synthetic context

This module ports the structural part of the historical synthetic-spectrum
interface.  A concrete model supplies the category and its explicit
compatibility fields; no functor, cofiber, or enrichment is selected globally.
The derived cofiber facts live in `Proofs.lean`.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy

attribute [local instance] HasZeroObject.zero'

universe u v u' v'

/-- A stable category with a coherent bigraded suspension and deformation map.

The parent class supplies the additive, shifted, monoidal, and triangulated
structure.  `biShift` records the extra synthetic grading, while `lam` is the
natural transformation
`Σ^(0,-1) ⟶ Id` used to define the λ-power quotients.
-/
class SyntheticCategory (Syn : Type u) extends
    StableHomotopyCategory.{u, v} Syn where
  biShift : ℤ × ℤ → Syn ⥤ Syn
  biShift_comp : ∀ (a b : ℤ × ℤ),
    biShift a ⋙ biShift b ≅ biShift (a + b)
  biShift_zero : biShift (0, 0) ≅ 𝟭 Syn
  biShift_compat : ∀ n : ℤ, biShift (n, 0) ≅ shiftFunctor Syn n
  /-- Each bigraded suspension is fully faithful (the inverse suspension is
      supplied by the same coherence data in a concrete model). -/
  biShift_fullyFaithful : ∀ p : ℤ × ℤ, (biShift p).FullyFaithful
  lam : biShift (0, -1) ⟶ 𝟭 Syn
  biShift_tensor_comm : ∀ (p : ℤ × ℤ) (X Y : Syn),
    (biShift p).obj (MonoidalCategory.tensorObj X Y) ≅
      MonoidalCategory.tensorObj ((biShift p).obj X) Y

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The `n`-fold composite of the deformation map `λ` on `X`.

The recursive definition follows the coherence isomorphism supplied by
`biShift_comp`; in particular `lambdaPow 0 X` is the chosen identity
isomorphism from `Σ^(0,0)X` to `X`.
-/
noncomputable def lambdaPow : (n : ℕ) → (X : Syn) →
    (SyntheticCategory.biShift (0, -(n : ℤ))).obj X ⟶ X
  | 0, X => SyntheticCategory.biShift_zero.hom.app X
  | n + 1, X => by
      have step1 :
          (SyntheticCategory.biShift ((0 : ℤ), -1) ⋙
            SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ))).obj X ⟶ X :=
        (SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ))).map
            (SyntheticCategory.lam.app X) ≫ lambdaPow n X
      have step2 :
          (SyntheticCategory.biShift ((0, -1) + (0, -(n : ℤ)))).obj X ⟶ X :=
        (SyntheticCategory.biShift_comp (0, -1) (0, -(n : ℤ))).inv.app X ≫ step1
      have heq :
          ((0 : ℤ), (-1 : ℤ)) + ((0 : ℤ), -(n : ℤ)) =
            ((0 : ℤ), -(↑(n + 1) : ℤ)) := by
        simp
      exact heq ▸ step2

/-- The chosen cofiber of `λ_X`. -/
noncomputable def XModLambda (X : Syn) [HasFunctorialCofiber (C := Syn)] : Syn :=
  HasFunctorialCofiber.cofib (SyntheticCategory.lam.app X)

/-- The chosen cofiber of `λⁿ_X`. -/
noncomputable def XModLambdaN (X : Syn) (n : ℕ)
    [HasFunctorialCofiber (C := Syn)] : Syn :=
  HasFunctorialCofiber.cofib (lambdaPow n X)

/-- The explicit ν-interface from a stable category into the synthetic one.

The compatibility fields are hypotheses supplied by a concrete construction;
they are deliberately stored in a record instead of declared as axioms.
-/
structure NuFunctorData (Stable : Type u) [StableHomotopyCategory.{u, v} Stable]
    (Syn : Type u') [SyntheticCategory.{u', v'} Syn] where
  functor : Stable ⥤ Syn
  additive : functor.Additive
  zeroIso : functor.obj 0 ≅ (0 : Syn)
  suspensionIso : ∀ X : Stable,
    functor.obj ((shiftFunctor Stable (1 : ℤ)).obj X) ≅
      (SyntheticCategory.biShift (1, 1)).obj (functor.obj X)

end KIP126.Synthetic.Context
