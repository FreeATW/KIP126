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

end KIP126.Core.SpectralSequence
