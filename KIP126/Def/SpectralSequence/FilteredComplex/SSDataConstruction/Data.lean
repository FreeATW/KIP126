import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs
import KIP126.Def.SpectralSequence.FilteredDifferential.Data

/-!
# Nested-subobject spectral sequence of a filtered complex

This is the construction layer connecting KIP126's canonical filtered complex
to the migrated `SSData`/`PreSS`/`SpectralSequence` API.  Its proof fields reuse
the already separated finite-page results; no property is postulated.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- The nested cycle/boundary data of a bounded filtered complex at `(s,k)`. -/
@[reducible] noncomputable def toSSData (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) : SSData C where
  V := FC.assocGraded s k
  Z := FC.cycleSubobject s k
  B := FC.boundarySubobject s k
  Z_anti := FC.cycleSubobject_antitone s k
  B_mono := FC.boundarySubobject_monotone s k
  Z_zero := FC.cycleSubobject_zero s k
  B_le_Z := FC.B_le_Z_aux s k
  Z_top_greatest := FC.cycleSubobject_top_greatest
    bnd.toAlgebra.toIsBoundedAbove s k
  B_top_least := FC.boundarySubobject_top_least
    bnd.toAlgebra.toIsBoundedBelow s k

set_option maxHeartbeats 6400000 in
/-- The data-only pre-spectral sequence of a bounded filtered complex. -/
noncomputable def toPreSS (FC : FilteredComplex C)
    (bnd : FC.IsBounded) : PreSS C (ℤ × ℤ) where
  r₀ := 0
  ssData := fun ⟨s, k⟩ => FC.toSSData bnd s k
  diffDeg := fun r => (r, -1)
  d := fun r ⟨s, k⟩ =>
    if hr : 0 ≤ r then
      eqToHom (by
        have hnat : (r - 0).toNat = r.toNat := by omega
        rw [hnat]
        simp [SSData.page, FilteredComplex.toSSData,
          FilteredComplex.pageObj]) ≫
        FC.pageDifferential s k r.toNat ≫
        eqToHom (by
          have hnat : (r - 0).toNat = r.toNat := by omega
          have hrnat : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr
          rw [hnat, hrnat]
          simp [SSData.page, FilteredComplex.toSSData,
            FilteredComplex.pageObj]
          rw [show k - 1 = k + -1 by omega])
    else 0

end FilteredComplex

end KIP126.Core.SpectralSequence
