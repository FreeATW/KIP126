import KIP126.Def.ClassicalAdams.MilnorCooperations.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Proofs
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Standard sphere Adams classes from specified Milnor cocycles
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

namespace Sphere

variable (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- Send a specified normalized Milnor cocycle through the actual first-page
homology quotient and page-passage map to `E₂`. -/
def classOfMilnorCocycle (s t : ℕ) (x : KIP126.Steenrod.Milnor.cochains s t)
    (hx : KIP126.Steenrod.Milnor.differential s t x = 0) :
    ((mod2SphereAdams H).page 2 (by decide)).X ((s : ℤ), (t : ℤ)) := by
  let K := adamsPageComplex H.unit SphereSpectrum 1 (by decide)
  let p : ℤ × ℤ := (s, t)
  let q : ℤ × ℤ := ((s + 1 : ℕ), t)
  let a : K.X p := (M.coordinates s t).symm x
  have hpq : (classicalAdamsShape 1).next p = q := by
    apply ComplexShape.next_eq'
    change p + ((1 : ℤ), 1 - 1) = q
    dsimp [p, q]
    apply Prod.ext <;> simp
  have ha : (K.d p q).hom a = 0 := milnorCocycle_d_zero H M s t x hx
  exact (adamsPageHomologyIso H.unit SphereSpectrum 1 (by decide) p).hom
    ((K.homologyπ p).hom (K.cyclesMk a q hpq ha))

/-- The standard sphere Adams class `h₆`, represented by `[ξ₁^64]`. -/
def h6 : ((mod2SphereAdams H).page 2 (by decide)).X (1, 64) :=
  classOfMilnorCocycle H M 1 64 KIP126.Steenrod.Milnor.h6Cochain
    KIP126.Steenrod.Milnor.h6Cochain_isCycle

/-- The square of the standard `h₆`: the class of the concatenation product
`[ξ₁^64 | ξ₁^64]`, in filtration two and internal degree 128. -/
def h6Square : ((mod2SphereAdams H).page 2 (by decide)).X (2, 128) :=
  classOfMilnorCocycle H M 2 128 KIP126.Steenrod.Milnor.h6SquareCochain
    KIP126.Steenrod.Milnor.h6SquareCochain_isCycle

end Sphere

end

end KIP126.Classical.Adams
