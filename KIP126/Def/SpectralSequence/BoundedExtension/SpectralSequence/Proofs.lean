import KIP126.Def.SpectralSequence.BoundedExtension.SpectralSequence.Data
import KIP126.Def.SpectralSequence.Convergence.SSData.Proofs

/-!
# Page-zero calculations for bounded extensions
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem BoundedExtensionSS.e0PageAtOne_eq
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (s : ℤ) :
    ext.e0PageAtOne t s = F₁.associatedGraded s t := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem BoundedExtensionSS.e0PageAtZero_eq
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (s : ℤ) :
    ext.e0PageAtZero t s = F₂.associatedGraded s t := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- The page-zero differential is the associated-graded map induced by the
target map of the convergence morphism. -/
theorem BoundedExtensionSS.d0_eq_inducedAssocGradedMap
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (s : ℤ) :
    ext.d0 t s =
      eqToHom (ext.e0PageAtOne_eq t s) ≫
        Filtration.inducedAssocGradedMap cm.aMap cm.filtration_compat s t ≫
        eqToHom (ext.e0PageAtZero_eq t s).symm := by
  have hOne : eqToHom (ext.e0PageAtOne_eq t s) = 𝟙 _ := by rfl
  have hZero : eqToHom (ext.e0PageAtZero_eq t s).symm = 𝟙 _ := by rfl
  rw [hOne, hZero, Category.id_comp, Category.comp_id]
  change (underlyingComplex cm.aMap cm.filtration_compat t).assocGradedDiff s 1 =
    Filtration.inducedAssocGradedMap cm.aMap cm.filtration_compat s t
  letI : Epi (F₁.toAssociatedGraded s t) := by
    unfold Filtration.toAssociatedGraded
    infer_instance
  apply (cancel_epi (F₁.toAssociatedGraded s t)).mp
  rw [underlyingComplex_assocGradedDiff_compat_one]
  unfold Filtration.inducedAssocGradedMap cokernel.map
  simp only [Filtration.toAssociatedGraded, cokernel.π_desc]

end KIP126.Core.SpectralSequence
