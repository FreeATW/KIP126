import KIP126.Def.SpectralSequence.Commutativity

/-!
# Regression checks for extension-square commutativity
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
variable {ω' : Type w}

example (sq : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω')) :
    sq.f ≫ sq.q = sq.p ≫ sq.g :=
  sq.comm

#check ESSNoCrossing
#check ESSNoCrossingRange
#check detectionGradedProj

#print axioms ess_ssData_V
#print axioms ess_diffDeg
#print axioms HomotopyCommSquare.toSquare_comm
#print axioms essCommutativity_filtration_compat
#print axioms detectionGradedProj_compat

end KIP126.Core.SpectralSequence
