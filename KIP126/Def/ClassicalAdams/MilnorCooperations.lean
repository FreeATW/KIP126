import KIP126.Def.ClassicalAdams.Mod2Sphere
import KIP126.Def.Steenrod.MilnorCobar
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Milnor cooperations and standard sphere Adams classes

The accepted abstract `H𝔽₂` foundation includes its normalized Milnor
coordinates on the first page of its Adams resolution.  The compatibility
law below identifies the **constructed** first differential with the explicit
Milnor coproduct differential.  Merely specifying `π₀ H𝔽₂` and vanishing of
its other homotopy groups would not supply this foundation.

All later pages come from the tower construction.  In particular, the input
does not contain an `E₂` page, an `h` family, a product, or a permanence claim.
The standard second-page classes are constructed by applying the actual
page-passage map to specified Milnor cocycles.
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The already constructed `d₁`, restricted to nonnegative bidegrees. -/
def sphereFirstDifferential (H : Mod2EilenbergMacLane (C := C)) (s t : ℕ) :
    adamsPage H.unit SphereSpectrum 1 (by decide) s t →ₗ[ℤ]
      adamsPage H.unit SphereSpectrum 1 (by decide) (s + 1 : ℕ) t :=
  ((adamsPageComplex H.unit SphereSpectrum 1 (by decide)).d
    ((s : ℤ), (t : ℤ)) (((s + 1 : ℕ) : ℤ), (t : ℤ))).hom

/-- The normalized Milnor cooperation structure of the abstract `H𝔽₂`
foundation, on its constructed resolution.  These coordinates and their
coproduct compatibility are the explicit extra foundational input. -/
structure MilnorCooperations (H : Mod2EilenbergMacLane (C := C)) where
  coordinates : ∀ s t : ℕ,
    adamsPage H.unit SphereSpectrum 1 (by decide) s t ≃ₗ[ℤ]
      KIP126.Steenrod.Milnor.cochains s t
  differential_coordinates : ∀ (s t : ℕ)
      (x : adamsPage H.unit SphereSpectrum 1 (by decide) s t),
    coordinates (s + 1) t (sphereFirstDifferential H s t x) =
      KIP126.Steenrod.Milnor.differential s t (coordinates s t x)

namespace Sphere

variable (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- A specified Milnor cocycle is a cycle in the actual first Adams page. -/
theorem milnorCocycle_d_zero (s t : ℕ) (x : KIP126.Steenrod.Milnor.cochains s t)
    (hx : KIP126.Steenrod.Milnor.differential s t x = 0) :
    sphereFirstDifferential H s t ((M.coordinates s t).symm x) = 0 := by
  apply (M.coordinates (s + 1) t).injective
  rw [M.differential_coordinates, LinearEquiv.apply_symm_apply, hx, map_zero]

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
