import KIP126.Def.SpectralSequence.Extension.Proofs

/-!
# The canonical two-term complex
-/

namespace KIP126.Core.SpectralSequence.BoundedExtension

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [CategoryTheory.Category.{v} C] [Abelian C]

/-- The canonical chain complex carried by a two-term differential. -/
noncomputable def twoTermComplex (X₁ X₂ : C) (f : X₁ ⟶ X₂) : ChainComplex C ℤ :=
  ChainComplex.of
    (twoTermObj X₁ X₂)
    (fun k => twoTermDiff X₁ X₂ f (k + 1) ≫
      eqToHom (congrArg (twoTermObj X₁ X₂) (by omega : (k + 1) - 1 = k)))
    (fun k => by
      exact twoTermDiff_sq_transport X₁ X₂ f (k + 1 + 1) (k + 1) k
        (by omega) (by omega))

/-- Data for a bounded two-term extension at one graded stem.

The filtered complex is the canonical computational object.  The `two_term`
field records that no other chain degree contributes; endpoint and convergence
witnesses are supplied by the existing endpoint/convergence APIs when a
downstream construction needs them. -/
structure TwoTermData where
  complex : FilteredComplex C
  two_term : ∀ k : ℤ, k ≠ 1 → k ≠ 0 → IsZero (complex.complex.X k)

end KIP126.Core.SpectralSequence.BoundedExtension
