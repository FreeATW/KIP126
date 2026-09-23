import KIP126.Def.ClassicalESS.Eta.ExternalInput

namespace KIP126.Classical.ExtensionSS

open CategoryTheory CategoryTheory.Limits
open KIP126.Classical.Adams
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence
open KIP126.External

/-- A paper-specific extension relation on the concrete finite rows. -/
def FExtension {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) (row : EtaDifferential) : Prop :=
  row ∈ D.differentials

/-- Set-valued detection predicate for the concrete construction. -/
def DetectedBy {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) (row : EtaDifferential) : Prop :=
  row ∈ D.detected

/-- Essentiality is only defined for rows of this concrete eta construction. -/
def Essential {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) (row : EtaDifferential) : Prop :=
  FExtension D row ∧ row.essential = true

/-- A crossing is a pair of concrete rows with the prescribed filtration order. -/
def Crossing {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) (row : EtaDifferential) : Prop :=
  ∃ other, other ∈ D.differentials ∧ other.sourceFiltration > row.sourceFiltration ∧
    other.targetFiltration ≤ row.targetFiltration

def NoCrossing {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) (row : EtaDifferential) : Prop :=
  ¬ Crossing D row

end KIP126.Classical.ExtensionSS
