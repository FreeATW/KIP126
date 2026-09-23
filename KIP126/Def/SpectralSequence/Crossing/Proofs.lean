import KIP126.Def.SpectralSequence.Crossing.Predicates

/-! Proofs about differential relations in the `SSData` model. -/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- The ambient differential relation is equivalent to compatible page representatives. -/
theorem dr_apply_iff_rel
    (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V) :
    (∃ (x₀ : T ⟶ (E.ssData k).page
          (↑(r - E.r₀).toNat : WithTop ℕ))
        (y₀ : T ⟶ (E.ssData (k + E.diffDeg r)).page
          (↑(r - E.r₀).toNat : WithTop ℕ)),
      x₀ ≫ E.d r k = y₀ ∧
        ElementPageRel E r k x x₀ ∧
        ElementPageRel E r (k + E.diffDeg r) y y₀) ↔
      DifferentialRelation E r k x y := by
  constructor
  · rintro ⟨x₀, y₀, hxy, ⟨xZ, hxZ, hx₀⟩, ⟨yZ, hyZ, hy₀⟩⟩
    subst hx₀
    subst hy₀
    exact ⟨xZ, hxZ, yZ, hyZ, by rw [← Category.assoc]; exact hxy⟩
  · rintro ⟨xZ, hxZ, yZ, hyZ, hrel⟩
    exact ⟨
      xZ ≫ (E.ssData k).pageπ (↑(r - E.r₀).toNat : WithTop ℕ),
      yZ ≫ (E.ssData (k + E.diffDeg r)).pageπ
        (↑(r - E.r₀).toNat : WithTop ℕ),
      by rwa [Category.assoc],
      ⟨xZ, hxZ, rfl⟩,
      ⟨yZ, hyZ, rfl⟩⟩

end KIP126.Core.SpectralSequence
