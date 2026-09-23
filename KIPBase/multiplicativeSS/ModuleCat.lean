/-
  KIPBase.multiplicativeSS.ModuleCat

  Exactness facts needed to apply the homology-based associativity
  propagation theorem in categories of modules.
-/
import KIPBase.Mathlib
import KIPBase.multiplicativeSS.Basic

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

/-- Tensoring two epimorphisms of modules over a commutative ring again gives
an epimorphism.  This is the categorical form of right exactness of tensor
product used in `HomologyTripleQuotientEpi`. -/
theorem moduleCat_tensorHom_epi
    {R : Type u} [CommRing R] {M₁ M₂ N₁ N₂ : ModuleCat.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  change Function.Surjective (f ⊗ₘ g).hom
  rw [ModuleCat.hom_tensorHom]
  exact TensorProduct.map_surjective
    ((ModuleCat.epi_iff_surjective f).mp inferInstance)
    ((ModuleCat.epi_iff_surjective g).mp inferInstance)

/-- The left-associated tensor of three epimorphisms of modules is epic. -/
theorem moduleCat_tensorHom3_epi
    {R : Type u} [CommRing R]
    {M₁ M₂ N₁ N₂ P₁ P₂ : ModuleCat.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) (h : P₁ ⟶ P₂)
    [Epi f] [Epi g] [Epi h] : Epi ((f ⊗ₘ g) ⊗ₘ h) := by
  letI : Epi (f ⊗ₘ g) := moduleCat_tensorHom_epi f g
  exact moduleCat_tensorHom_epi (f ⊗ₘ g) h

/-- In a module category, the three quotient maps from cycles to homology
of arbitrary spectral sequences remain epic after tensoring. -/
theorem moduleCat_ssPageTripleQuotientEpi
    {R : Type u} [CommRing R] {ι : Type u} [AddCommGroup ι] [DecidableEq ι]
    (E₁ E₂ E₃ : SpectralSequence (ModuleCat.{u} R) ι) (r : ℤ) :
    SSPageTripleQuotientEpi E₁ E₂ E₃ r := by
  intro i j k
  exact moduleCat_tensorHom3_epi
    (E₁.pageShortComplex r (i - E₁.diffDeg r)).homologyπ
    (E₂.pageShortComplex r (j - E₂.diffDeg r)).homologyπ
    (E₃.pageShortComplex r (k - E₃.diffDeg r)).homologyπ

/-- The self-pairing specialization needed by
`MultiplicativeSS.isAssociativeAt_succ`. -/
theorem moduleCat_homologyTripleQuotientEpi
    {R : Type u} [CommRing R] {ι : Type u} [AddCommGroup ι] [DecidableEq ι]
    {E : SpectralSequence (ModuleCat.{u} R) ι} (P : MultiplicativeSS E)
    (r : ℤ) : ∀ i j k : ι,
      Epi
        (((E.pageShortComplex r (i - E.diffDeg r)).homologyπ ⊗ₘ
          (E.pageShortComplex r (j - E.diffDeg r)).homologyπ) ⊗ₘ
          (E.pageShortComplex r (k - E.diffDeg r)).homologyπ) :=
  moduleCat_ssPageTripleQuotientEpi E E E r

end KIPBase.SpectralSequence
