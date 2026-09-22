import KIP126.Def.ClassicalAdams.TowerSequence.PagePassage.Proofs

/-!
# The spectral sequence assembled from the Adams tower
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

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
