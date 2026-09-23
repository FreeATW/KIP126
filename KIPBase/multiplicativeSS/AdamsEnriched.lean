import KIPBase.Mathlib
import KIPBase.multiplicativeSS.Adams

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.MonoidalCategory KIPBase.SpectralSequence

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-- The category in which the converging mapping Adams spectral sequences take values. -/
abbrev AdamsConvergingSSCategory :=
  ConvergingSS (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ) ℤ

/-- Finite spectra, used as the objects of the Adams-enriched category. -/
abbrev FiniteSpectra (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮] :=
  { X : 𝒮 // IsFiniteSpectrum X }

/-- A converging-spectral-sequence enrichment of finite spectra whose enriched
Hom from `X` to `Y` is their converging mapping Adams spectral sequence.
The monoidal structure on converging spectral sequences is included because
it is not yet constructed elsewhere in the library. -/
structure AdamsSpectralSequenceEnrichment
    (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮] where
  monoidal : MonoidalCategory AdamsConvergingSSCategory.{v}
  enriched : @EnrichedCategory
    AdamsConvergingSSCategory.{v} _ monoidal (FiniteSpectra 𝒮)
  hom_eq : ∀ X Y : FiniteSpectra 𝒮,
    enriched.Hom X Y = adamsMappingConvergingSS X.1 Y.1 X.2 Y.2
  /-- An Adams composition pairing is represented by a morphism from the
  tensor product of the two mapping sequences. -/
  pairingEquiv :
    letI : MonoidalCategory AdamsConvergingSSCategory.{v} := monoidal;
    ∀ X Y Z : FiniteSpectra 𝒮,
      ConvergingSSPairing
        (adamsMappingConvergingSS X.1 Y.1 X.2 Y.2)
        (adamsMappingConvergingSS Y.1 Z.1 Y.2 Z.2)
        (adamsMappingConvergingSS X.1 Z.1 X.2 Z.2) ≃
      ((adamsMappingConvergingSS X.1 Y.1 X.2 Y.2 ⊗
        adamsMappingConvergingSS Y.1 Z.1 Y.2 Z.2) ⟶
        adamsMappingConvergingSS X.1 Z.1 X.2 Z.2)
  /-- Enriched composition is exactly the Adams pairing, after identifying
  the enriched Hom objects with the mapping Adams sequences. -/
  comp_eq :
    letI : MonoidalCategory AdamsConvergingSSCategory.{v} := monoidal;
    ∀ X Y Z : FiniteSpectra 𝒮,
      eqToHom (congrArg₂ (fun A B : AdamsConvergingSSCategory.{v} => A ⊗ B)
        (hom_eq X Y).symm (hom_eq Y Z).symm) ≫
        enriched.comp X Y Z ≫ eqToHom (hom_eq X Z) =
      pairingEquiv X Y Z
        (adamsCompositionConvergingSSPairing X.1 Y.1 Z.1 X.2 Y.2 Z.2)

/-- The Adams spectral sequence makes the category of finite spectra enriched
over the monoidal category of converging spectral sequences. -/
axiom adamsSpectralSequenceEnrichment :
  AdamsSpectralSequenceEnrichment 𝒮

end KIPBase.StableHomotopy
