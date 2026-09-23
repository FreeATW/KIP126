import KIP126.Def.SpectralSequence.BoundedExtension.TwoTerm.Proofs
import KIP126.Def.SpectralSequence.Extension.Complex.Proofs
import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs

/-!
# The filtered two-term complex of a filtration-compatible map
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- The two-term filtered complex `A₁(t) ⟶ A₂(t)` at a fixed stem. -/
noncomputable def underlyingComplex
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ φ : Subobject.underlying.obj (F₁.F s k') ⟶
          Subobject.underlying.obj (F₂.F s k'),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') : FilteredComplex C where
  complex := BoundedExtension.twoTermComplex (A₁ t) (A₂ t) (aMap t)
  filtration := {
    F := twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t)
    decreasing := fun s k => by
      by_cases h₁ : k = 1
      · subst k
        simpa [BoundedExtension.twoTermComplex, BoundedExtension.twoTermObj,
          twoTermFil, BoundedExtension.twoTermFil] using F₁.mono s t
      · by_cases h₀ : k = 0
        · subst k
          simpa [BoundedExtension.twoTermComplex, BoundedExtension.twoTermObj,
            twoTermFil, BoundedExtension.twoTermFil] using F₂.mono s t
        · simp [twoTermFil, BoundedExtension.twoTermFil, h₁, h₀] }
  differential_preserves := fun s k => by
    by_cases h : k = 1
    · subst k
      refine ⟨(hcompat s t).choose, ?_⟩
      simpa [BoundedExtension.twoTermDiff, BoundedExtension.twoTermFil,
        twoTermFil] using (hcompat s t).choose_spec
    · refine ⟨0, ?_⟩
      simp [BoundedExtension.twoTermDiff, BoundedExtension.twoTermFil,
        twoTermFil, h]

end KIP126.Core.SpectralSequence
