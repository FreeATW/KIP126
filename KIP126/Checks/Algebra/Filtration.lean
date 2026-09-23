import KIP126.Def.Algebra.Filtration.Proofs

/-!
# Regression checks for canonical filtration laws

These examples keep the migrated index-transport and Mittag-Leffler laws
visible to the checked surface without introducing a second filtration type.
-/

namespace KIP126.Core.Algebra

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

example [Abelian C] (F : Filtration A) {r₁ r₂ r₃ : ℤ × ι}
    (h₁₂ : r₁ = r₂) (h₂₃ : r₂ = r₃) :
    F.transportGraded h₁₂ ≫ F.transportGraded h₂₃ =
      F.transportGraded (h₁₂.trans h₂₃) :=
  F.transportGraded_trans h₁₂ h₂₃

example [Abelian C] (F : Filtration A) (hF : F.IsBoundedAbove) :
    F.IsMittagLeffler :=
  hF.isMittagLeffler

example [Abelian C] (F : Filtration A) (hF : F.IsBounded) :
    F.IsMittagLeffler :=
  hF.isMittagLeffler

end KIP126.Core.Algebra
