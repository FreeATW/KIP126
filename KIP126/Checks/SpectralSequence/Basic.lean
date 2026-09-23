import KIP126.Def.SpectralSequence.Basic

/-!
# API regression checks for nested-subobject spectral sequences

These checks pin the public declaration names migrated from
`KIPBase.SpectralSequence.Basic` without importing the historical component.
-/

namespace KIP126.Checks.SpectralSequence.Basic

open CategoryTheory
open KIP126.Core.SpectralSequence

#check SSData
#check SSData.Z
#check SSData.B
#check SSData.page
#check SSData.eInfty
#check SSData.pageπ
#check GradedComplex
#check PreSS
#check PreSS.Page
#check UnderlyingMorphism
#check SSDataMorphism
#check PreSSMorphism
#check SpectralSequence
#check SpectralSequence.ofPreSS
#check SpectralSequence.Page
#check SpectralSequence.pageGraded
#check SpectralSequence.pageShortComplex
#check SpectralSequence.pageHomologyIso
#check SpectralSequence.DegeneratesAt
#check SpectralSequenceMorphism
#check SpectralSequenceMorphism.eInftyMap
#check EInftyData
#check EInftyData.EInfty
#check GradedSSData
#check PreSS.forget
#check SpectralSequence.inclusion
#check SpectralSequence.CommSq

end KIP126.Checks.SpectralSequence.Basic
