import KIP126.Def.SpectralSequence.PageDifferential.Proofs

/-! Essentiality concerns a differential value, including for nonzero maps. -/

namespace KIP126.Checks.SpectralSequence.PageDifferential

open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.MathlibModel

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable (E : CategoryTheory.SpectralSequence C c r₀)
variable (r : ℤ) (hr : r₀ ≤ r) (source target : κ) {T : C}

example (x : PageElement c r₀ E r hr source T) :
    ¬ EssentialDifferentialRelation E r hr source target x (0 : T ⟶ _) := by
  rintro ⟨_, h⟩
  exact h rfl

example (y : PageElement c r₀ E r hr target T)
    (h : DifferentialRelation E r hr source target (0 : T ⟶ _) y) :
    y = 0 := by
  simpa only [DifferentialRelation, zero_comp] using h.symm

end KIP126.Checks.SpectralSequence.PageDifferential
