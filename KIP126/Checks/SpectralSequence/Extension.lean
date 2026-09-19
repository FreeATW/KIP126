import KIP126.Def.SpectralSequence.Extension.Data

/-!
# Regression checks for bounded extensions
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : CategoryTheory.GradedObject ℤ C}

example (F : Algebra.Filtration A) {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (i : ℤ) :
    F.quotientProjection (s₁ + 1) i ≫
        F.quotientTransition (show s₀ + 1 ≤ s₁ + 1 by omega) i =
      F.quotientProjection (s₀ + 1) i :=
  F.quotientProjection_transition (show s₀ + 1 ≤ s₁ + 1 by omega) i

example (F : Algebra.Filtration A) {s₀ s₁ s₂ : ℤ}
    (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ ≤ s₂) (i : ℤ) :
    F.quotientTransition (show s₁ + 1 ≤ s₂ + 1 by omega) i ≫
        F.quotientTransition (show s₀ + 1 ≤ s₁ + 1 by omega) i =
      F.quotientTransition (show s₀ + 1 ≤ s₂ + 1 by omega) i :=
  F.quotientTransition_comp (show s₀ + 1 ≤ s₁ + 1 by omega)
    (show s₁ + 1 ≤ s₂ + 1 by omega) i

example (D : BoundedExtension.TwoTermData (C := C))
    (k : ℤ) (hk₁ : k ≠ 1) (hk₀ : k ≠ 0) :
    IsZero (D.complex.complex.X k) :=
  D.two_term k hk₁ hk₀

example (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    BoundedExtension.twoTermDiff X₁ X₂ f k ≫
        BoundedExtension.twoTermDiff X₁ X₂ f (k - 1) = 0 :=
  BoundedExtension.twoTermDiff_sq X₁ X₂ f k

example (X₁ X₂ : C) (F₁ : ℤ → Subobject X₁) (F₂ : ℤ → Subobject X₂)
    (s : ℤ) :
    BoundedExtension.twoTermFil F₁ F₂ s 1 = F₁ s ∧
      BoundedExtension.twoTermFil F₁ F₂ s 0 = F₂ s := by
  exact ⟨BoundedExtension.twoTermFil_one F₁ F₂ s,
    BoundedExtension.twoTermFil_zero F₁ F₂ s⟩

end KIP126.Core.SpectralSequence
