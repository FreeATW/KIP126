import KIP126.Solution.Tools.generalized_leibniz

/-! Exact page-stretch endpoint over the typed extension operations. -/
namespace KIP126.Solution.Tools.PagePropagation

open KIP126.Solution.Tools.Thm6_1Leibniz

structure Input (O : Operations) where
  base : Thm6_1Leibniz.Input O
  noLoss : ∀ q : ℤ, base.n ≤ q → q ≤ base.r → Prop

theorem page_extension_stretch (I : Input O) :
  (∀ (q : ℤ) (h₁ : I.base.n ≤ q) (h₂ : q ≤ I.base.r),
      I.noLoss q h₁ h₂) →
    O.targetDifferential (I.base.r + I.base.l - I.base.m)
        (I.base.r - 1 - I.base.m + I.base.e)
        (I.base.s + I.base.m, I.base.t + I.base.m) I.base.y =
      transportTarget I.base.targetDegreeCoherence.symm I.base.yInfinity := by
  sorry

end KIP126.Solution.Tools.PagePropagation
