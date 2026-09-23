import KIP126.Def.SpectralSequence.FilteredComplex

namespace KIP126.Checks.SpectralSequence.FilteredComplexSSDataConstruction

open CategoryTheory CategoryTheory.Limits
open KIP126.Core.SpectralSequence

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (FC : FilteredComplex C) (bnd : FC.IsBounded)

#check FC.toSSData bnd
#check FC.toPreSS bnd
#check FC.toSpectralSequence bnd
#check FC.A
#check FC.d
#check FC.fil
#check FC.fil_anti
#check FC.d_preserves_fil
#check FC.assocGraded
#check FC.filToAssocGraded
#check FC.filDiff
#check FC.assocGradedDiff
#check FC.assocGradedDiff_compat
#check FC.assocGradedDiff_cast
#check FC.assocGradedDiff_sq
#check FC.homologyObj
#check FC.homologySSObj
#check FC.homologySSFiltration
#check FC.fil_anti_of_le
#check FC.dToK
#check FC.cycleSubobject
#check FC.boundarySubobject
#check FC.dToK_comp_d
#check FC.B_le_Z_aux
#check FC.pageDifferential
#check FC.pageDifferential_comp
#check FC.pageDifferential_Z_succ_ge
#check FC.pageDifferential_Z_succ_le
#check FC.pageDifferential_B_succ
#check FC.IsLift
#check FC.isLift_sub_factors
#check FC.weakConvergence bnd

example (s k : ℤ) (n : ℕ) :
    (FC.toPreSS bnd).d (n : ℤ) (s, k) = FC.pageDifferential s k n := by
  exact FC.toPreSS_d_nat bnd s k n

#print axioms KIP126.Core.SpectralSequence.FilteredComplex.toSSData
#print axioms KIP126.Core.SpectralSequence.FilteredComplex.toPreSS
#print axioms KIP126.Core.SpectralSequence.FilteredComplex.toSpectralSequence
#print axioms KIP126.Core.SpectralSequence.FilteredComplex.isLift_sub_factors
#print axioms KIP126.Core.SpectralSequence.FilteredComplex.weakConvergence

end KIP126.Checks.SpectralSequence.FilteredComplexSSDataConstruction
