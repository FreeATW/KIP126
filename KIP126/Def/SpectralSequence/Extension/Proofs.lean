import KIP126.Def.SpectralSequence.Extension.Data

/-!
# Proofs for two-term extension data
-/

namespace KIP126.Core.SpectralSequence.BoundedExtension

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [CategoryTheory.Category.{v} C] [Abelian C]

@[simp]
lemma twoTermObj_one (X₁ X₂ : C) : twoTermObj X₁ X₂ 1 = X₁ := by
  simp [twoTermObj]

@[simp]
lemma twoTermObj_zero (X₁ X₂ : C) : twoTermObj X₁ X₂ 0 = X₂ := by
  simp [twoTermObj]

lemma twoTermObj_other (X₁ X₂ : C) (k : ℤ) (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    twoTermObj X₁ X₂ k = ⊥_ C := by
  simp [twoTermObj, h₁, h₀]

@[simp]
lemma twoTermDiff_sq (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    twoTermDiff X₁ X₂ f k ≫ twoTermDiff X₁ X₂ f (k - 1) = 0 := by
  simp only [twoTermDiff]
  by_cases h : k = 1
  · subst k
    change _ ≫ (0 : twoTermObj X₁ X₂ 0 ⟶ twoTermObj X₁ X₂ (-1)) = 0
    simp only [comp_zero]
  · simp [h]

@[simp]
lemma twoTermFil_one {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 1 = fil₁ s := by
  simp [twoTermFil]

@[simp]
lemma twoTermFil_zero {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 0 = fil₂ s := by
  simp [twoTermFil]

lemma twoTermDiff_sq_transport (X₁ X₂ : C) (f : X₁ ⟶ X₂)
    (a b c : ℤ) (hab : a - 1 = b) (hbc : b - 1 = c) :
    (twoTermDiff X₁ X₂ f a ≫ eqToHom (congrArg (twoTermObj X₁ X₂) hab)) ≫
        twoTermDiff X₁ X₂ f b ≫ eqToHom (congrArg (twoTermObj X₁ X₂) hbc) = 0 := by
  subst b
  subst c
  simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
    twoTermDiff_sq X₁ X₂ f a

end KIP126.Core.SpectralSequence.BoundedExtension
