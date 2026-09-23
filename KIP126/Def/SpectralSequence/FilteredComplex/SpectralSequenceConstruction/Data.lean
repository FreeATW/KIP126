import KIP126.Def.SpectralSequence.FilteredComplex.SSDataConstruction.Proofs
import KIP126.Def.SpectralSequence.FilteredDifferential.Proofs

/-!
# Spectral-sequence assembly for a filtered complex

The data are supplied by `FilteredComplex.toPreSS`; this layer discharges the
three spectral-sequence laws using the finite-page proofs.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

set_option maxHeartbeats 6400000 in
/-- The nested-subobject spectral sequence canonically built from a bounded
filtered complex. -/
noncomputable def toSpectralSequence (FC : FilteredComplex C)
    (bnd : FC.IsBounded) : SpectralSequence C (ℤ × ℤ) :=
  SpectralSequence.ofPreSS (FC.toPreSS bnd)
    (fun r ⟨s, k⟩ => by
      by_cases hr : 0 ≤ r
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
        simp only [FC.toPreSS_d_nat bnd]
        change FC.pageDifferential s k n ≫
          FC.pageDifferential (s + ↑n) (k - 1) n = 0
        exact FC.pageDifferential_comp s k n
      · dsimp only [FilteredComplex.toPreSS]
        rw [dif_neg hr]
        exact zero_comp)
    (fun r ⟨s, k⟩ hr => by
      have hr0 : 0 ≤ r := by
        simpa only [FilteredComplex.toPreSS] using hr
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
      simp only [FC.toPreSS_d_nat bnd]
      change kernelSubobject (FC.pageDifferential s k n) =
        imageSubobject (Subobject.ofLE
          (FC.cycleSubobject s k ↑(n + 1)) (FC.cycleSubobject s k ↑n)
          (FC.cycleSubobject_antitone s k
            (by exact_mod_cast Nat.le_succ n)) ≫ FC.pageπ s k ↑n)
      apply le_antisymm
      · exact pageDifferential_Z_succ_le FC s k n
      · exact pageDifferential_Z_succ_ge FC s k n)
    (fun r ⟨s, k⟩ hr => by
      have hr0 : 0 ≤ r := by
        simpa only [FilteredComplex.toPreSS] using hr
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
      simp only [FC.toPreSS_d_nat bnd]
      change imageSubobject (FC.pageDifferential s k n) =
        imageSubobject (Subobject.ofLE
          (FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1))
          (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)
          (le_trans (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑(n + 1))
            (FC.cycleSubobject_antitone (s + ↑n) (k - 1)
              (by exact_mod_cast Nat.le_succ n))) ≫
          FC.pageπ (s + ↑n) (k - 1) ↑n)
      exact FC.pageDifferential_B_succ s k n)

end FilteredComplex

end KIP126.Core.SpectralSequence
