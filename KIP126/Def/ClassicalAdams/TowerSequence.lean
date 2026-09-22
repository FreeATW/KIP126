import KIP126.Def.ClassicalAdams.TowerDifferential

/-!
# The spectral sequence constructed from an Adams tower

The page-passage map sends an `(r+1)`-cycle to the homology class of its
image on page `r`.  Its inverse is obtained by inverting that specified
linear map.  The unresolved exact-couple proofs are marked with `sorry`;
neither a page-passage isomorphism nor a spectral sequence is an input.
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- A cycle which lifts one stage farther is in particular an `r`-cycle. -/
theorem adamsCycles_succ_le (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unit X (r + 1) (by omega) s t ≤ adamsCycles unit X r hr s t := by
  sorry

/-- The image of a next-page cycle in the current quotient page. -/
def adamsNextCycleToPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unit X (r + 1) (by omega) s t →ₗ[ℤ] adamsPage unit X r hr s t :=
  (adamsCycleBoundaries unit X r hr s t).mkQ.comp
    (Submodule.inclusion (adamsCycles_succ_le unit X r hr s t))

/-- The current-page image of a next-page cycle is killed by the differential. -/
theorem adamsNextCycle_d_zero (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (x : adamsCycles unit X (r + 1) (by omega) p.1 p.2) :
    ((adamsPageComplex unit X r hr).sc p).g
      (adamsNextCycleToPage unit X r hr p.1 p.2 x) = 0 := by
  sorry

/-- The specified map from next-page representatives to current-page cycles. -/
def adamsNextCycleToKernel (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsCycles unit X (r + 1) (by omega) p.1 p.2 →ₗ[ℤ]
      LinearMap.ker ((adamsPageComplex unit X r hr).sc p).g.hom :=
  (adamsNextCycleToPage unit X r hr p.1 p.2).codRestrict _
    (adamsNextCycle_d_zero unit X r hr p)

/-- The homology class of a next-page representative. -/
def adamsNextCycleToHomology (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsCycles unit X (r + 1) (by omega) p.1 p.2 →ₗ[ℤ]
      ((adamsPageComplex unit X r hr).sc p).moduleCatLeftHomologyData.H :=
  (LinearMap.range ((adamsPageComplex unit X r hr).sc p).moduleCatToCycles).mkQ.comp
    (adamsNextCycleToKernel unit X r hr p)

/-- Next-page boundaries become current-page homology boundaries. -/
theorem adamsNextBoundaries_le_ker (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsCycleBoundaries unit X (r + 1) (by omega) p.1 p.2 ≤
      LinearMap.ker (adamsNextCycleToHomology unit X r hr p) := by
  sorry

/-- The page-passage map, from the next page to the homology of the current page. -/
def adamsNextPageToHomology (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsPage unit X (r + 1) (by omega) p.1 p.2 →ₗ[ℤ]
      ((adamsPageComplex unit X r hr).sc p).moduleCatLeftHomologyData.H :=
  (adamsCycleBoundaries unit X (r + 1) (by omega) p.1 p.2).liftQ
    (adamsNextCycleToHomology unit X r hr p)
    (adamsNextBoundaries_le_ker unit X r hr p)

/-- Exact-couple page passage is bijective. -/
theorem adamsNextPageToHomology_bijective (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    Function.Bijective (adamsNextPageToHomology unit X r hr p) := by
  sorry

/-- The page-passage isomorphism obtained by inverting the specified quotient map. -/
def adamsPageHomologyIso (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    (adamsPageComplex unit X r hr).homology p ≅
      adamsPageObject unit X (r + 1) (by omega) p :=
  ((adamsPageComplex unit X r hr).sc p).moduleCatHomologyIso ≪≫
    (LinearEquiv.ofBijective (adamsNextPageToHomology unit X r hr p)
      (adamsNextPageToHomology_bijective unit X r hr p)).toModuleIso.symm

/-- The Adams tower's quotient-page construction as a Mathlib spectral
sequence, displayed from page two.  Integer modules retain the underlying
abelian groups without assuming a mod-two structure for an arbitrary `H`. -/
def adamsTowerSpectralSequence :
    CategoryTheory.SpectralSequence (ModuleCat.{v} ℤ) classicalAdamsShape 2 where
  page r hr := by
    cases r with
    | ofNat n =>
      have hn : 1 ≤ n := by
        change (2 : ℤ) ≤ (n : ℤ) at hr
        omega
      exact adamsPageComplex unit X n hn
    | negSucc n => omega
  iso r r' p hrr' hr := by
    subst r'
    cases r with
    | ofNat n =>
      have hn : 1 ≤ n := by
        change (2 : ℤ) ≤ (n : ℤ) at hr
        omega
      exact adamsPageHomologyIso unit X n hn p
    | negSucc n => omega

end

end KIP126.Classical.Adams
