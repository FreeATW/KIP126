import KIP126.Challenge.Tools.Thm6_1Leibniz.Statement

/-! Exact page-stretch endpoint over the typed extension operations. -/
namespace KIP126.Challenge.Tools.PagePropagation

open KIP126.Challenge.Tools.Thm6_1Leibniz

structure Input (O : Operations) where
  base : Thm6_1Leibniz.Input O
  noLoss : ∀ q : ℤ, base.n ≤ q → q ≤ base.r → Prop

def statement {O : Operations} (I : Input O) : Prop :=
  (∀ (q : ℤ) (h₁ : I.base.n ≤ q) (h₂ : q ≤ I.base.r),
      I.noLoss q h₁ h₂) →
    conclusion I.base

end KIP126.Challenge.Tools.PagePropagation
