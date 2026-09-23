import KIPBase.multiplicativeSS.adamsdata.adamsE2
import KIPBase.multiplicativeSS.AdamsDetection

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.Pretriangulated

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-- The sphere, regarded as a finite spectrum. -/
private abbrev S : FiniteSpectra 𝒮 :=
  ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩

/-- The degree-zero stable homotopy class twice the identity of the sphere. -/
noncomputable def sphereTwo : (AdamsDetection.A (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))).A 0 :=
  (adamsMappingConvergingSS_abutmentEquiv (𝒮 := 𝒮) SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere 0).symm
    ((mappingSpectrumHomotopy (𝒮 := 𝒮) 0 SphereSpectrum SphereSpectrum).symm
      ((2 : ℤ) • (shiftFunctorZero 𝒮 ℤ).hom.app SphereSpectrum))

/-- The Hopf classes in stems `1`, `3`, and `7`, together with the assertions
that `h₀`, `h₁`, `h₂`, and `h₃` detect `2`, `η`, `ν`, and `σ`, respectively.
The classes and detection assertions are input data; no calculation of stable
homotopy groups is claimed here. -/
class SphereHopfData [AdamsE2Data.{u, v} 𝒮] where
  eta : (AdamsDetection.A (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))).A 1
  nv : (AdamsDetection.A (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))).A 3
  sigma : (AdamsDetection.A (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))).A 7
  two_detected : AdamsDetection.DetectsAbutment (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))
    2 (1, 1) (SpectralSequence.pageTransfer
      (AdamsSS 𝒮 SphereSpectrum) 2 (1, 1) (AdamsE2Data.hi 0)) (by
      rw [show ((AdamsDetection.A (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))).conv.reindex
        (1, 1)).2 = 0 from by
        have h := (adamsMappingConvergingSS_reindex (𝒮 := 𝒮)
          SphereSpectrum SphereSpectrum IsFiniteSpectrum.sphere
          IsFiniteSpectrum.sphere (1, 1)).2
        simpa using h]
      exact sphereTwo)
  eta_detected : AdamsDetection.DetectsAbutment (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))
    2 (1, 2) (SpectralSequence.pageTransfer
      (AdamsSS 𝒮 SphereSpectrum) 2 (1, 2) (AdamsE2Data.hi 1)) (by
      rw [show ((AdamsDetection.A (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))).conv.reindex
        (1, 2)).2 = 1 from by
        have h := (adamsMappingConvergingSS_reindex (𝒮 := 𝒮)
          SphereSpectrum SphereSpectrum IsFiniteSpectrum.sphere
          IsFiniteSpectrum.sphere (1, 2)).2
        simpa using h]
      exact eta)
  nv_detected : AdamsDetection.DetectsAbutment (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))
    2 (1, 4) (SpectralSequence.pageTransfer
      (AdamsSS 𝒮 SphereSpectrum) 2 (1, 4) (AdamsE2Data.hi 2)) (by
      rw [show ((AdamsDetection.A (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))).conv.reindex
        (1, 4)).2 = 3 from by
        have h := (adamsMappingConvergingSS_reindex (𝒮 := 𝒮)
          SphereSpectrum SphereSpectrum IsFiniteSpectrum.sphere
          IsFiniteSpectrum.sphere (1, 4)).2
        simpa using h]
      exact nv)
  sigma_detected : AdamsDetection.DetectsAbutment (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))
    2 (1, 8) (SpectralSequence.pageTransfer
      (AdamsSS 𝒮 SphereSpectrum) 2 (1, 8) (AdamsE2Data.hi 3)) (by
      rw [show ((AdamsDetection.A (S (𝒮 := 𝒮)) (S (𝒮 := 𝒮))).conv.reindex
        (1, 8)).2 = 7 from by
        have h := (adamsMappingConvergingSS_reindex (𝒮 := 𝒮)
          SphereSpectrum SphereSpectrum IsFiniteSpectrum.sphere
          IsFiniteSpectrum.sphere (1, 8)).2
        simpa using h]
      exact sigma)

end KIPBase.StableHomotopy
