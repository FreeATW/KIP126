import KIP126.Def.SpectralSequence.Extension.Complex.Data

/-!
# Proofs for the canonical two-term complex
-/

namespace KIP126.Core.SpectralSequence.BoundedExtension

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [CategoryTheory.Category.{v} C] [Abelian C]

@[simp]
lemma twoTermComplex_X (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    (twoTermComplex X₁ X₂ f).X k = twoTermObj X₁ X₂ k := by
  simp [twoTermComplex]

@[simp]
lemma twoTermComplex_d (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    (twoTermComplex X₁ X₂ f).d k (k - 1) = twoTermDiff X₁ X₂ f k := by
  unfold twoTermComplex
  change ChainComplex.of.d (twoTermObj X₁ X₂)
      (fun j => twoTermDiff X₁ X₂ f (j + 1) ≫
        eqToHom (congrArg (twoTermObj X₁ X₂) (by omega : (j + 1) - 1 = j)))
      k (k - 1) = twoTermDiff X₁ X₂ f k
  unfold ChainComplex.of.d
  rw [dif_pos (show k = k - 1 + 1 by omega)]
  simp

@[simp]
lemma twoTermComplex_d_one (X₁ X₂ : C) (f : X₁ ⟶ X₂) :
    (twoTermComplex X₁ X₂ f).d 1 0 = f := by
  simpa [twoTermDiff, twoTermObj] using twoTermComplex_d X₁ X₂ f 1

end KIP126.Core.SpectralSequence.BoundedExtension
