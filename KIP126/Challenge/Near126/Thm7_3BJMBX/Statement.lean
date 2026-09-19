import KIP126.Def.Kervaire.Theta5.Predicates
import KIP126.External.Literature.Kervaire

/-!
# Theorem 7.3: BJM/BX criterion for every order-two choice

The near-126 definition layer owns the carrier, the square, the `lambda eta`
map, and the finite quotient predicates.  This file only states the project
transport target over that canonical interface.  The source criterion and the
choice-filtration input are explicit `CataloguedExternalResult` values; no
choice-independence fact is assumed here.
-/

namespace KIP126.Challenge.Near126.Thm7_3BJMBX

open KIP126.External
open KIP126.Kervaire

/-! ## Typed input and target -/

/-- The fixed near-126 input for the project transport.  `criterion` is the
Burklund--Xu result at the distinguished source choice, while `order` carries
the separate Xu/IWX order and choice-filtration result. -/
structure Input {Carrier : Type} [AddCommGroup Carrier] where
  context : Theta5ChoiceContext (Carrier := Carrier)
  criterion : CataloguedExternalResult (BJM_BXCriterion context)
  order : CataloguedExternalResult (Theta5OrderData context)

/-- The exact Theorem 7.3 target.  For every admissible order-two synthetic
choice `theta5`, `h₆²` survives to `E_(r+3)` precisely when the displayed
`lambda eta theta5²` class vanishes modulo `lambda^(r+1)`, and permanence is
equivalent to vanishing in the untruncated sphere.  The `Int.toNat` coercions
make the paper's integer parameter explicit while retaining the natural-number
quotient indices of the canonical finite-quotient interface. -/
def anyChoiceCriterion {Carrier : Type} [AddCommGroup Carrier]
    (I : Input (Carrier := Carrier)) : Prop :=
  ∀ (theta5 : Carrier), I.context.isChoice theta5 →
    IsOrderTwo theta5 →
      (∀ (r : ℤ), 1 ≤ r →
        (I.context.h6Survives (Int.toNat (r + 3)) ↔
          I.context.finiteZero (Int.toNat (r + 1))
            (I.context.lambdaEta (I.context.square theta5)))) ∧
      (I.context.h6Permanent ↔
        I.context.untruncatedZero
          (I.context.lambdaEta (I.context.square theta5)))

end KIP126.Challenge.Near126.Thm7_3BJMBX
