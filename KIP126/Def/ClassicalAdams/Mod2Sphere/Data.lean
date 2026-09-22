import KIP126.Def.ClassicalAdams.TowerSequence.Data
import KIP126.Def.StableHomotopy.Cohomology.Data

/-!
# The Adams spectral sequence of the sphere

Specialize the actual tower construction to the sphere, with the unit of
the mod-two Eilenberg–Mac Lane spectrum.  This definition contains no
input page, product, named generator, or intermediate Kervaire proposition.

The underlying groups are represented as integer modules.  Identifying the
second page with the Steenrod Ext algebra, and thereby introducing its
standard generators and multiplication, is a separate unfinished construction.
-/

namespace KIP126.Classical.Adams

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The sphere's mod-two Adams spectral sequence, constructed from its tower. -/
noncomputable def mod2SphereAdams (H : Mod2EilenbergMacLane (C := C)) :
    CategoryTheory.SpectralSequence (ModuleCat.{v} ℤ) classicalAdamsShape 2 :=
  adamsTowerSpectralSequence H.unit SphereSpectrum

end KIP126.Classical.Adams
