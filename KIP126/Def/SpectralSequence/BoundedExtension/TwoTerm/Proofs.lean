import KIP126.Def.SpectralSequence.BoundedExtension.TwoTerm.Data
import KIP126.Def.SpectralSequence.Extension.Proofs

/-!
# Proofs for historical two-term extension data
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

@[simp]
lemma twoTermObj_one (X₁ X₂ : C) : twoTermObj X₁ X₂ 1 = X₁ := by
  exact BoundedExtension.twoTermObj_one X₁ X₂

@[simp]
lemma twoTermObj_zero' (X₁ X₂ : C) : twoTermObj X₁ X₂ 0 = X₂ := by
  exact BoundedExtension.twoTermObj_zero X₁ X₂

lemma twoTermObj_other (X₁ X₂ : C) (k : ℤ) (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    twoTermObj X₁ X₂ k = ⊥_ C := by
  exact BoundedExtension.twoTermObj_other X₁ X₂ k h₁ h₀

theorem twoTermDiff_sq (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    twoTermDiff X₁ X₂ f k ≫ twoTermDiff X₁ X₂ f (k - 1) = 0 := by
  exact BoundedExtension.twoTermDiff_sq X₁ X₂ f k

@[simp]
lemma twoTermFil_one {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 1 = fil₁ s := by
  exact BoundedExtension.twoTermFil_one fil₁ fil₂ s

@[simp]
lemma twoTermFil_zero' {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 0 = fil₂ s := by
  exact BoundedExtension.twoTermFil_zero fil₁ fil₂ s

end KIP126.Core.SpectralSequence
