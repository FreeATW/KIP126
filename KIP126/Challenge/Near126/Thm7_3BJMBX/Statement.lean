import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.External.Provenance

/-!
# Theorem 7.3: BJM/BX criterion for every order-two choice

This file records the exact transport target used by the near-126 argument.
The source BJM/BX criterion is an explicit `ExternalResult`; the statement
below quantifies over all synthetic choices satisfying the order-two and
`h₅²` detection conditions.  No choice-independence fact is assumed here: it
is the open project theorem represented by `anyChoiceCriterion`.
-/

namespace KIP126.Challenge.Near126.Thm7_3BJMBX

open KIP126.Classical.Adams
open KIP126.External

/-! ## Typed input data -/

/-- The homotopy groups and operations needed to write the two BJM/BX
expressions.  The quotient index is the exponent of `λ`; index `0` is the
untruncated synthetic sphere.  A concrete synthetic construction supplies
this record and its grading laws. -/
structure SyntheticSphereData where
  Homotopy : ℤ → ℤ → ℕ → Type
  zero : ∀ (stem weight : ℤ) (quotient : ℕ), Homotopy stem weight quotient
  add : ∀ (stem weight : ℤ) (quotient : ℕ),
    Homotopy stem weight quotient → Homotopy stem weight quotient →
      Homotopy stem weight quotient
  eta : Homotopy 1 2 0
  thetaSquare : Homotopy 62 64 0 → Homotopy 62 64 0 →
    Homotopy 124 128 0
  etaMultiply : Homotopy 1 2 0 → Homotopy 124 128 0 →
    Homotopy 125 130 0
  lambda : Homotopy 125 130 0 → Homotopy 125 129 0
  quotientMap : ∀ (exponent : ℕ),
    Homotopy 125 129 0 → Homotopy 125 129 exponent
  detectsH5Square : Homotopy 62 64 0 → Prop

/-- A synthetic representative of `θ₅` with precisely the hypotheses used by
Theorem 7.3: it is detected by `h₅²` and has exact additive order two. -/
structure Theta5Choice (S : SyntheticSphereData) where
  value : S.Homotopy 62 64 0
  detected : S.detectsH5Square value
  nonzero : value ≠ S.zero 62 64 0
  orderTwo : S.add 62 64 0 value value = S.zero 62 64 0

/-- The expression `ληθ₅²`, with its source and target tridegrees fixed by the
paper. -/
def theta5Expression (S : SyntheticSphereData) (choice : Theta5Choice S) :
    S.Homotopy 125 129 0 :=
  S.lambda (S.etaMultiply S.eta (S.thetaSquare choice.value choice.value))

/-- The chosen classical $h_6^2$ page class and the two survival predicates
used by the criterion.  The class is constructed from the named sphere
presentation, so the statement cannot be instantiated at an unrelated page
or spectrum. -/
structure ClassicalH6SquareData where
  stable : StableHomotopyContext
  sequence : ClassicalAdamsSS stable stable.sphere
  presentation : SphereAdamsPresentation sequence
  survivesTo : AdamsClass sequence → ℤ → Prop
  permanent : AdamsClass sequence → Prop

namespace ClassicalH6SquareData

/-- The page-2 product representing $h_6^2$. -/
def h6Square (D : ClassicalH6SquareData) : AdamsClass D.sequence :=
  sphereProduct D.presentation (D.presentation.h 6) (D.presentation.h 6)

theorem h6Square_degree (D : ClassicalH6SquareData) :
    (D.h6Square).degree = (2, 128) := by
  rw [h6Square, sphereProduct]
  rw [D.presentation.multiplication.product_degree]
  simp only [D.presentation.h_degree]
  norm_num

end ClassicalH6SquareData

/-! ## External criterion and the project target -/

/-- The proposition supplied by Burklund--Xu for one distinguished order-two
choice.  It is kept separate from the project transport to every choice. -/
def distinguishedCriterion
    (D : ClassicalH6SquareData) (S : SyntheticSphereData)
    (choice : Theta5Choice S) : Prop :=
  (∀ (r : ℤ), 1 ≤ r →
      D.survivesTo D.h6Square (r + 3) ↔
        S.quotientMap (Int.toNat (r + 1)) (theta5Expression S choice) =
          S.zero 125 129 (Int.toNat (r + 1))) ∧
    (D.permanent D.h6Square ↔
      theta5Expression S choice = S.zero 125 129 0)

/-- A fixed near-126 input for Theorem 7.3.  The external result is explicitly
source-tagged as Burklund--Xu; the theorem below still has to transport it from
the distinguished source choice to every admissible choice. -/
structure Input where
  classical : ClassicalH6SquareData
  synthetic : SyntheticSphereData
  distinguished : Theta5Choice synthetic
  bjmBx : ExternalResult
    (distinguishedCriterion classical synthetic distinguished)
  bjmBx_source : bjmBx.ref.source = SourceId.burklundXu

/-- The exact Theorem 7.3 target: every order-two synthetic `θ₅` choice obeys
both the finite-quotient and untruncated BJM/BX equivalences. -/
def anyChoiceCriterion (I : Input) : Prop :=
  ∀ (choice : Theta5Choice I.synthetic),
    (∀ (r : ℤ), 1 ≤ r →
      I.classical.survivesTo I.classical.h6Square (r + 3) ↔
        I.synthetic.quotientMap (Int.toNat (r + 1))
            (theta5Expression I.synthetic choice) =
          I.synthetic.zero 125 129 (Int.toNat (r + 1))) ∧
    (I.classical.permanent I.classical.h6Square ↔
      theta5Expression I.synthetic choice = I.synthetic.zero 125 129 0)

end KIP126.Challenge.Near126.Thm7_3BJMBX
