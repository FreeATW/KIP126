import KIP126.Def.SpectralSequence.Convergence.SSData

/-! API regression checks for the migrated nested-subobject convergence layer. -/

namespace KIP126.Checks.SpectralSequence.ConvergenceSSData

open KIP126.Core.SpectralSequence

#check Filtration
#check Filtration.F
#check Filtration.mono
#check Filtration.associatedGraded
#check Filtration.toAssociatedGraded
#check Filtration.transportGraded
#check Filtration.IsBounded
#check Filtration.IsBoundedBelow
#check Filtration.IsBoundedAbove
#check Filtration.IsExhaustive
#check Filtration.IsHausdorff
#check Convergence
#check Convergence.filtrationDegree
#check Convergence.stemDegree
#check ConvergenceMorphismData
#check ConvergenceMorphism
#check Detects
#check detect_zero
#check detect_difference
#check FilteredMorphism
#check FilteredMorphism.inducedGrMap
#check ConvergingSS

end KIP126.Checks.SpectralSequence.ConvergenceSSData
