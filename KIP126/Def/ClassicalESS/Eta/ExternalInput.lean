import KIP126.Def.ClassicalESS.Eta.Data
import KIP126.External.Claims

/-! Provenance-bearing input and the resulting concrete classical eta ESS. -/

namespace KIP126.Classical.ExtensionSS

open CategoryTheory CategoryTheory.Limits
open KIP126.Classical.Adams
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence
open KIP126.External

structure EtaESSInput {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y) where
  adapter : ClassicalEtaESSAdapter source target
  differentials : Set EtaDifferential
  detected : Set EtaDifferential
  detected_eq_differentials : detected = differentials
  ledgerEvidence : KIP126.External.CataloguedExternalEvidence
    (KIP126.Classical.Regression.etaEss differentials)
  pageData : EtaESSPageData adapter differentials
  pageIso : ∀ (n : ℤ) (b : Index),
    (etaPage pageData n).homology b ≅ (etaPage pageData (n + 1)).X b

/-- The abutment is displayed componentwise as kernel plus cokernel. -/
noncomputable def abutment {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) : GradedObject Index Coeff :=
  fun b => kernel (D.adapter.etaMap b) ⊞ cokernel (D.adapter.etaMap b)

/-- The concrete classical eta-ESS returned by this module. -/
noncomputable def etaESS {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (D : EtaESSInput source target) :
    SpectralSequence Coeff etaESSShape 0 where
  page n _ := etaPage D.pageData n
  iso n _ b _ _ := D.pageIso n b

end KIP126.Classical.ExtensionSS
