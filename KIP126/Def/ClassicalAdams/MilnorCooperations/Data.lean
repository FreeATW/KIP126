import KIP126.Def.ClassicalAdams.Mod2Sphere.Data
import KIP126.Def.Steenrod.MilnorCobar.Data

/-!
# # Milnor cooperations and standard sphere Adams classes

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

end

end KIP126.Classical.Adams
