import KIP126.Def.SpectralSequence.Extension.Data

/-!
# Historical two-term extension data

The public names are kept in `KIP126.Core.SpectralSequence`; their
implementations delegate to the canonical two-term data already present in
`BoundedExtension`.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The graded object supported in degrees `1` and `0`. -/
noncomputable def twoTermObj (X₁ X₂ : C) : ℤ → C :=
  BoundedExtension.twoTermObj X₁ X₂

/-- The differential whose sole potentially nonzero component is `f`. -/
noncomputable def twoTermDiff (X₁ X₂ : C) (f : X₁ ⟶ X₂) :
    (k : ℤ) → twoTermObj X₁ X₂ k ⟶ twoTermObj X₁ X₂ (k - 1) :=
  BoundedExtension.twoTermDiff X₁ X₂ f

/-- The two-term filtration inherited from the source and target. -/
noncomputable def twoTermFil {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) :
    ℤ → (k : ℤ) → Subobject (twoTermObj X₁ X₂ k) :=
  BoundedExtension.twoTermFil fil₁ fil₂

end KIP126.Core.SpectralSequence
