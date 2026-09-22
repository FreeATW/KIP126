import KIP126.Def.ClassicalAdams.Tower
import KIP126.Def.StableHomotopy.Context.Proofs
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotient pages of the Adams tower

These are the usual exact-couple formulas, expressed using the actual tower
maps.  They do not take a spectral sequence or its pages as inputs.  A page
class in bidegree `(s,t)` has stem `t-s`.

For `r ≥ 1`, `Zᵣ` is the inverse image, under the connecting map, of the
image from tower stage `s+r`.  The boundary subgroup `Bᵣ` is the image in the
layer of the kernel of the map from stage `s` to stage `s-r+1`.  The quotient
page is `Zᵣ / (Zᵣ ∩ Bᵣ)`; exactness implies `Bᵣ ≤ Zᵣ`.
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

variable {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The underlying group of the first page. -/
abbrev adamsE1 (s t : ℤ) := HomotopyGroup (t - s) (adamsLayerAt unit X s)

/-- The tower-to-layer map in the exact couple. -/
def adamsJ (s t : ℤ) :
    HomotopyGroup (t - s) (adamsTowerAt unit X s) →ₗ[ℤ] adamsE1 unit X s t :=
  (inducedMap (HasFunctorialCofiber.cofibι
    (adamsTowerMapAt unit X s (s + 1) (by omega))) (t - s)).toIntLinearMap

/-- The connecting map in the exact couple. -/
noncomputable def adamsK (s t : ℤ) :
    adamsE1 unit X s t →ₗ[ℤ]
      HomotopyGroup (t - s - 1) (adamsTowerAt unit X (s + 1)) :=
  (connectingHomomorphism (HoCofiberSequence.ofMorphism
    (adamsTowerMapAt unit X s (s + 1) (by omega))) (t - s)).toIntLinearMap

/-- A composite of tower maps on a fixed homotopy group. -/
def adamsI (n s t : ℤ) (h : s ≤ t) :
    HomotopyGroup n (adamsTowerAt unit X t) →ₗ[ℤ]
      HomotopyGroup n (adamsTowerAt unit X s) :=
  (inducedMap (adamsTowerMapAt unit X s t h) n).toIntLinearMap

/-- The `r`-cycle submodule in the first page. -/
def adamsCycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    Submodule ℤ (adamsE1 unit X s t) :=
  (LinearMap.range (adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega))).comap
    (adamsK unit X s t)

/-- The `r`-boundary submodule in the first page. -/
def adamsBoundaries (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    Submodule ℤ (adamsE1 unit X s t) :=
  (LinearMap.ker (adamsI unit X (t - s) (s - r + 1) s (by omega))).map
    (adamsJ unit X s t)

/-- Boundaries regarded as a submodule of the cycle module. -/
def adamsCycleBoundaries (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    Submodule ℤ (adamsCycles unit X r hr s t) :=
  (adamsBoundaries unit X r hr s t).comap (adamsCycles unit X r hr s t).subtype

/-- The quotient group on page `r`, constructed from the Adams tower. -/
abbrev adamsPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :=
  (adamsCycles unit X r hr s t) ⧸ adamsCycleBoundaries unit X r hr s t

/-- Lift the connecting image of an `r`-cycle along `r-1` tower maps.
Existence is exactly the defining membership condition of `adamsCycles`.
This makes a choice of a representative, not of a page or differential. -/
noncomputable def adamsCycleLift (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    HomotopyGroup (t - s - 1) (adamsTowerAt unit X (s + r)) :=
  Classical.choose x.property

theorem adamsCycleLift_spec (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega)
      (adamsCycleLift unit X r hr s t x) = adamsK unit X s t x :=
  Classical.choose_spec x.property

/-- A tower-to-layer image is an `r`-cycle on every page. -/
theorem adamsJ_mem_cycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (y : HomotopyGroup (t - s) (adamsTowerAt unit X s)) :
    adamsJ unit X s t y ∈ adamsCycles unit X r hr s t := by
  change adamsK unit X s t (adamsJ unit X s t y) ∈ LinearMap.range _
  refine ⟨0, ?_⟩
  rw [map_zero]
  symm
  exact (les_homotopy_exact_g
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (t - s) _).mpr ⟨y, rfl⟩

/-- Reindex the lift to the target bidegree of the Adams differential. -/
noncomputable def adamsDifferentialLift (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    HomotopyGroup ((t + r - 1) - (s + r)) (adamsTowerAt unit X (s + r)) :=
  Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + r)))
    (by omega : t - s - 1 = (t + r - 1) - (s + r)))
    (adamsCycleLift unit X r hr s t x)

/-- The differential formula `j(lift(k(x)))`, evaluated in the target
quotient.  Descending this function to a linear map on `adamsPage` requires
the independence-of-lift and boundary calculations. -/
noncomputable def adamsDifferentialValue (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    adamsPage unit X r hr (s + r) (t + r - 1) :=
  (adamsCycleBoundaries unit X r hr (s + r) (t + r - 1)).mkQ
    ⟨adamsJ unit X (s + r) (t + r - 1) (adamsDifferentialLift unit X r hr s t x),
      adamsJ_mem_cycles unit X r hr (s + r) (t + r - 1) _⟩

end

end KIP126.Classical.Adams
