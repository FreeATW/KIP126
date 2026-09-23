import KIP126.Def.SpectralSequence.PageDifferential.Predicates

/-! Basic, proof-carrying facts for page differential relations. -/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

namespace MathlibModel

theorem differentialRelation_iff (E : SpectralSequence C c r₀) (r : ℤ)
    (hr : r₀ ≤ r) (source target : κ) {T : C}
    (x : PageElement c r₀ E r hr source T)
    (y : PageElement c r₀ E r hr target T) :
    DifferentialRelation E r hr source target x y ↔
      x ≫ PageDifferential c r₀ E r hr source target = y := by
  rfl

theorem essentialDifferentialRelation_isEssential
    (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r)
    (source target : κ) {T : C}
    {x : PageElement c r₀ E r hr source T}
    {y : PageElement c r₀ E r hr target T}
    (h : EssentialDifferentialRelation E r hr source target x y) :
    y ≠ 0 := h.2

theorem noCrossing_iff (D : DifferentialDatum (c := c) (r₀ := r₀) E) :
    NoCrossing (C := C) (c := c) (r₀ := r₀) D ↔
      NoCrossingRange (C := C) (c := c) (r₀ := r₀) D
        (D.filtrationDegree D.source + 1) := by
  rfl

theorem not_hasCrossingAt_of_noCrossing (D : DifferentialDatum (c := c) (r₀ := r₀) E)
    (h : NoCrossing (C := C) (c := c) (r₀ := r₀) D) :
    ¬ HasCrossingAt (C := C) (c := c) (r₀ := r₀) D
        (D.filtrationDegree D.source + 1) := by
  intro hc
  apply h
  rcases hc with ⟨a, ha, r', hr', source', target', hsource, hessential,
    htarget, hbound⟩
  exact ⟨a, ha, r', hr', source', target', hsource, hessential,
    htarget ▸ le_rfl, hbound⟩

end MathlibModel

end KIP126.Core.SpectralSequence
