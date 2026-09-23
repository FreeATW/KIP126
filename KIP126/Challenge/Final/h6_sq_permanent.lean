import KIP126.Def.ClassicalAdams.SphereClasses.Data
import KIP126.Def.SpectralSequence.Permanence.Data

/-!
# The permanent `h₆²` proof target

This theorem records the statement with its proof left as `sorry`.  The sphere
Adams sequence and the class are constructed from the abstract stable
foundation and its explicitly specified Milnor cooperations.  No near-126
condition, differential exclusion, or intermediate theorem is an input.

The proof is not implemented; this declaration is an open Challenge theorem,
not a completed result.
-/
namespace KIP126.Challenge.Final.H6SquarePermanent

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams

universe u v

/-- The standard `h₆² ∈ E₂^{2,128}(S⁰)` has compatible nonzero descendants
on every later page of the constructed sphere Adams spectral sequence. -/
theorem h6_sq_permanent {C : Type u} [StableHomotopyCategory.{u, v} C]
    [HasFunctorialCofiber (C := C)]
    (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H) :
  KIP126.Core.SpectralSequence.IsPermanent
    (mod2SphereAdams H) 2 (by decide) (2, 128) (Sphere.h6Square H M) := by
  sorry

end KIP126.Challenge.Final.H6SquarePermanent
