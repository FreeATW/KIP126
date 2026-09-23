import KIP126.Def.ClassicalAdams.Convergence.Proofs
import KIP126.Def.SpectralSequence.PageLevel.Proofs
import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.External.Literature.Adams.OneLine

/-!
# Regression checks for the first classical Adams slice

The h₄ calculation is an explicit external input.  The regression therefore
checks its degree, Mathlib page passage, and catalogue provenance for every
chosen sphere presentation carrying that input; it does not manufacture the
literature calculation as a project axiom.
-/

namespace KIP126.Classical.Adams.Regression

open CategoryTheory KIP126.External

example : classicalAdamsPageLevel.firstPage = 2 := rfl
example : classicalAdamsPageLevel.admissibleFrom = 2 := rfl
example (r : ℕ) : classicalAdamsPageLevel.page r = r := rfl
example (r : ℕ) : classicalAdamsPageLevel.cycleLevel r = (r : ℤ) - 1 := rfl
example (r : ℕ) :
    classicalAdamsPageLevel.cycleLevel r =
      classicalAdamsPageLevel.quotientExponent r :=
  classicalAdamsPageLevel.cycleLevel_eq_quotientExponent r
example (r : ℕ) (h : 2 ≤ r) :
    classicalAdamsPageLevel.admissibleFrom ≤ classicalAdamsPageLevel.page r :=
  classicalAdamsPageLevel.page_ge h

example {G : CategoryTheory.GradedObject ℤ AddCommGrpCat}
    (F : KIP126.Core.Algebra.Filtration G)
    (hF : F.IsEventuallyZero) :
    IsAdamsFiltrationSeparated F :=
  isAdamsFiltrationSeparated_of_eventuallyZero F hF

variable {stable : StableHomotopyContext}
  {A : ClassicalAdamsSS stable stable.sphere}

example (P : SphereAdamsPresentation A)
    (input : CataloguedExternalResult (KIP126.Classical.adamsOneLineDifferentials P)) :
    input.value.InventoryValid :=
  CataloguedExternalResult.inventoryValid input

example :
    classicalAdamsTarget 2 (1, 16) = (3, 17) := by
  norm_num [classicalAdamsTarget, classicalAdamsShift]

example (P : SphereAdamsPresentation A)
    (proof : adamsOneLineDifferentials P) :
    (cataloguedAdamsOneLine P proof).value.ref.locator.artifact =
      some "aimpaper/main.tex" := by
  let input := cataloguedAdamsOneLine P proof
  change input.value.ref.locator.artifact = some "aimpaper/main.tex"
  rw [input.ref_eq]
  rfl

example (b : Bidegree) :
    (classicalAdamsShape 2).Rel b (classicalAdamsTarget 2 b) :=
  classicalAdamsShape_two_rel b

example (b : Bidegree) :
    (A.E₂).homology b ≅ (A.E₃).X b :=
  A.e₂ToE₃ b

example (P : SphereAdamsPresentation A)
    (proof : KIP126.Classical.adamsOneLineDifferentials P) :
    ∃ statement : AdamsD₂Statement A,
      statement.source = P.h 4 ∧
        statement.target = sphereProduct P (P.h 0)
          (sphereProduct P (P.h 3) (P.h 3)) ∧
        statement.source.degree = (1, 16) ∧
        statement.target.degree = (3, 17) :=
  KIP126.Classical.adamsOneLineDifferentials_h₄_degrees P proof

example :
    (externalClaimLedger.lookup .adamsOneLine).owner =
      `KIP126.Classical.adamsOneLineDifferentials := rfl

example :
    (externalClaimLedger.lookup .adamsOneLine).classification =
      .compositeResult := rfl

example (P : SphereAdamsPresentation A)
    (proof : KIP126.Classical.adamsOneLineDifferentials P) :
    (cataloguedAdamsOneLine P proof).root = .adamsOneLine := rfl

/-! ### Spectrum-bound strong convergence -/

variable {π₂ : TwoCompleteStableHomotopy stable} {X : stable.Spectrum}
  (system : SpectrumBoundClassicalAdamsSS π₂ X)

example : KIP126.Core.Algebra.Filtration (π₂.groups X) :=
  system.strongConvergence.filtration

example : system.strongConvergence.filtration.IsExhaustive :=
  system.strongConvergence.exhaustive

example : IsAdamsFiltrationSeparated system.strongConvergence.filtration :=
  system.strongConvergence.separated

example (b : Bidegree) (r : ℤ)
    (hr : system.strongConvergence.stablePage b ≤ r) :
    UnderlyingAdamsPage system.pageSlice.sequence r
        ((system.strongConvergence.stablePage_ge_two b).trans hr) b ≅
      system.strongConvergence.filtration.associatedGraded b.1 (adamsStem b) :=
  system.strongConvergence.pageComparison b r hr

/-! ### Lawful, nondegenerate sphere multiplication -/

variable {sphereSystem : SpectrumBoundClassicalAdamsSS π₂ stable.sphere}

example (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P) (j : ℕ) :
    (P.h j).representative ≠ 0 :=
  algebra.h_nonzero j

example (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P) :
    (sphereProduct P (P.h 0)
      (sphereProduct P (P.h 3) (P.h 3))).representative ≠ 0 :=
  algebra.h₀h₃Squared_nonzero

example (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P)
    (a b : Bidegree) (x x' : (sphereSystem.pageSlice.E₂).X a)
    (y : (sphereSystem.pageSlice.E₂).X b) :
    algebra.productMap a b (x + x') y =
      algebra.productMap a b x y + algebra.productMap a b x' y := by
  simp

example {smashSphere : ClassicalAdamsSS stable
      (stable.smash stable.sphere stable.sphere)}
    (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P)
    (pairing : ExternalAdamsPairing sphereSystem.pageSlice
      sphereSystem.pageSlice smashSphere)
    (pairingLaws : ExternalAdamsPairingLaws pairing)
    (compatibility : SphereAdamsExternalCompatibility algebra pairing pairingLaws)
    (a b : Bidegree) (x : (sphereSystem.pageSlice.E₂).X a)
    (y : (sphereSystem.pageSlice.E₂).X b) :
    algebra.productMap a b x y =
      (compatibility.smashToSphere (a + b)).hom
        (pairingLaws.pairMap a b x y) :=
  compatibility.product_eq_external a b x y

/-! ### Located-result consumption -/

example (P : SphereAdamsPresentation A)
    (input : CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P)) :
    ∃ statement : AdamsD₂Statement A,
      statement.source = P.h 4 ∧
        statement.target = sphereProduct P (P.h 0)
          (sphereProduct P (P.h 3) (P.h 3)) ∧
        statement.source.degree = (1, 16) ∧
        statement.target.degree = (3, 17) :=
  cataloguedAdamsOneLine_h₄_degrees P input

example (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P)
    (input : CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P)) :
    H₄D₂Bound sphereSystem P algebra :=
  cataloguedAdamsOneLine_h₄_degrees_bound sphereSystem P algebra
    (cataloguedAdamsOneLineCanonical P input.value.proof)

example (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (input : AdamsOneLineCatalogue P) :
    input.value.ref = (externalClaimLedger.lookup .adamsOneLine).ref ∧
      (externalClaimLedger.lookup .adamsOneLine).owner =
        `KIP126.Classical.adamsOneLineDifferentials ∧
      (externalClaimLedger.lookup .adamsOneLine).classification =
        .compositeResult ∧
      (externalClaimLedger.lookup .adamsOneLine).ref.locator.artifact =
        some "aimpaper/main.tex" := by
  exact ⟨input.ref_eq, rfl, rfl, rfl⟩

example (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P)
    (input : CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P)) :
    IsAdamsFiltrationSeparated sphereSystem.strongConvergence.filtration ∧
      (P.h 4).representative ≠ 0 ∧
      (sphereProduct P (P.h 0)
        (sphereProduct P (P.h 3) (P.h 3))).representative ≠ 0 := by
  rcases cataloguedAdamsOneLine_h₄_degrees_bound sphereSystem P algebra
    (cataloguedAdamsOneLineCanonical P input.value.proof) with
    ⟨bound⟩
  have hSeparated := bound.strongConvergence.separated
  rw [bound.strongConvergence_eq] at hSeparated
  have hSourceNonzero := bound.lawfulAlgebra.h_nonzero 4
  have hTargetNonzero := bound.lawfulAlgebra.h₀h₃Squared_nonzero
  exact ⟨hSeparated, hSourceNonzero, hTargetNonzero⟩

end KIP126.Classical.Adams.Regression
