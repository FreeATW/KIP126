import KIP126.Def.SpectralSequence.FilteredComplex.SSDataConstruction.Data

/-!
# Interface proofs for filtered-complex `PreSS` data
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- On a displayed natural-number page, the `PreSS` differential is exactly
the canonical finite-page differential. -/
@[simp]
theorem toPreSS_d_nat (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (s k : ℤ) (n : ℕ) :
    (FC.toPreSS bnd).d (n : ℤ) (s, k) = FC.pageDifferential s k n := by
  dsimp only [FilteredComplex.toPreSS]
  rw [dif_pos (Int.natCast_nonneg n)]
  change (eqToHom _ : FC.pageObj s k (↑n : WithTop ℕ) ⟶
      FC.pageObj s k ↑n) ≫
    FC.pageDifferential s k n ≫
      (eqToHom _ : FC.pageObj (s + ↑n) (k - 1) ↑n ⟶
        FC.pageObj (s + ↑n) (k - 1) ↑n) =
    FC.pageDifferential s k n
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

end FilteredComplex

end KIP126.Core.SpectralSequence
