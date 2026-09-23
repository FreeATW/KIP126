import KIP126.Def.SpectralSequence.FilteredDifferential.Helpers
import KIP126.Def.SpectralSequence.FilteredPage.Proofs

/-! The finite-page differential squares to zero. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

open DifferentialHelpers

set_option backward.isDefEq.respectTransparency false in
theorem pageDifferential_comp (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    FC.pageDifferential s k n ≫ FC.pageDifferential (s + ↑n) (k - 1) n = 0 := by
  set f₁ := Subobject.ofLE (FC.boundarySubobject s k ↑n) (FC.cycleSubobject s k ↑n)
    (FC.B_le_Z_aux s k ↑n)
  haveI : Epi (cokernel.π f₁) := inferInstance
  rw [show FC.pageDifferential s k n ≫ FC.pageDifferential (s + ↑n) (k - 1) n =
    FC.pageDifferential s k n ≫ FC.pageDifferential (s + ↑n) (k - 1) n from rfl]
  rw [← cancel_epi (cokernel.π f₁), comp_zero, ← Category.assoc]
  erw [cokernel.π_desc]
  set f_n₁ := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫ cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
  set kerZ₁ := kernelSubobject f_n₁
  set ι₁ := Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.decreasing s k)
  set πV₁ := cokernel.π ι₁
  set p₁ := factorThruImageSubobject (kerZ₁.arrow ≫ πV₁)
  haveI : Epi p₁ := inferInstance
  rw [← cancel_epi p₁, comp_zero, ← Category.assoc]
  erw [Abelian.comp_epiDesc]
  rw [Category.assoc]
  erw [cokernel.π_desc]
  rw [Category.assoc]
  erw [Abelian.comp_epiDesc]
  simp only [Category.assoc]
  erw [show ∀ {A' B' C' D' : C} (f : A' ⟶ B') (g : B' ⟶ C') (h : C' ⟶ D'),
    f ≫ (g ≫ h) = (f ≫ g) ≫ h from fun f g h => (Category.assoc f g h).symm]
  suffices h_zero : _ ≫ _ = (0 : _ ⟶ Subobject.underlying.obj (kernelSubobject
    ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow ≫ FC.complex.d (k - 1 - 1) (k - 1 - 1 - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n + ↑n + ↑n) (k - 1 - 1 - 1)).arrow)))) by
    erw [h_zero, zero_comp]
  apply (inferInstance : Mono (kernelSubobject
    ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow ≫ FC.complex.d (k - 1 - 1) (k - 1 - 1 - 1) ≫
      cokernel.π ((FC.filtration.F (s + ↑n + ↑n + ↑n) (k - 1 - 1 - 1)).arrow))).arrow).right_cancellation
  simp only [zero_comp, Category.assoc]
  erw [factorThruKernelSubobject_comp_arrow]
  apply (inferInstance : Mono (FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow).right_cancellation
  simp only [zero_comp, Category.assoc]
  erw [Abelian.monoLift_comp]
  conv_lhs => erw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
  conv_lhs => erw [← Category.assoc, Abelian.monoLift_comp]
  erw [Category.assoc, Category.assoc, FC.complex.d_comp_d k, comp_zero, comp_zero]

end KIP126.Core.SpectralSequence.FilteredComplex
