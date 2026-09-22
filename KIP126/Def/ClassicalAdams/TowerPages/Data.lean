import KIP126.Def.ClassicalAdams.Tower.Data
import KIP126.Def.StableHomotopy.Context.Proofs
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotient pages and lifts of the Adams tower
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

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

/-- Reindex the lift to the target bidegree of the Adams differential. -/
noncomputable def adamsDifferentialLift (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    HomotopyGroup ((t + r - 1) - (s + r)) (adamsTowerAt unit X (s + r)) :=
  Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + r)))
    (by omega : t - s - 1 = (t + r - 1) - (s + r)))
    (adamsCycleLift unit X r hr s t x)

end

end KIP126.Classical.Adams
