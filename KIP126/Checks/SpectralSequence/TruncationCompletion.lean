import KIP126.Def.SpectralSequence.Completion

/-!
# Legacy truncation and completion API checks

This file checks that the recognizable nested-subobject filtration API remains
available after migration and records the axiom footprint of its main results.
-/

namespace KIP126.Checks.SpectralSequence.TruncationCompletion

open CategoryTheory CategoryTheory.Limits
open KIP126.Core.SpectralSequence

#check Filtration.truncatedObj
#check Filtration.truncationProj
#check Filtration.truncatedFiltration
#check Filtration.truncationTransition
#check ConvergenceMorphism.truncatedAMap

#check Filtration.completionFunctor
#check Filtration.completion
#check Filtration.completionProj'
#check Filtration.toCompletion
#check Filtration.completionFiltration
#check Filtration.IsMittagLeffler
#check Filtration.IsBoundedAbove.toIsMittagLeffler
#check Filtration.completionLift
#check Filtration.completion_isComplete

#print axioms Filtration.IsBoundedAbove.toIsMittagLeffler
#print axioms Filtration.completion_isComplete

end KIP126.Checks.SpectralSequence.TruncationCompletion
