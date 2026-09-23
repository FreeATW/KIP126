import KIP126.Def.StableHomotopy.Context.Proofs

/-! Mapping-spectrum and sphere-smash consequences of a closed stable context. -/
namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory Pretriangulated

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [ClosedSymmetricTensorTriangulated (C := C)]

private noncomputable def smashDesuspIso (A B : C) :
    (shiftFunctor C (-1 : ℤ)).obj A ⊗ B ≅
      (shiftFunctor C (-1 : ℤ)).obj (A ⊗ B) :=
  (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).symm.app _ ≪≫
    (shiftFunctor C (-1 : ℤ)).mapIso (
      (ClosedSymmetricTensorTriangulated.smashSuspIso
        ((shiftFunctor C (-1 : ℤ)).obj A) B).symm ≪≫
      (tensorRight B).mapIso
        ((shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by omega)).app A) ≪≫
      eqToIso (by simp [Functor.id_obj, tensorRight]))

/-- Tensoring with a sphere implements the shift. -/
noncomputable def sphere_tensor_shift (n : ℤ) (X : C) :
    (Sphere n : C) ⊗ X ≅ (shiftFunctor C n).obj X :=
  Int.inductionOn' n 0
    (((tensorRight X).mapIso ((shiftFunctorZero C ℤ).app SphereSpectrum)) ≪≫
      (λ_ X) ≪≫ ((shiftFunctorZero C ℤ).app X).symm)
    (fun k _ ih =>
      ((tensorRight X).mapIso ((shiftFunctorAdd C k 1).app SphereSpectrum)) ≪≫
      ClosedSymmetricTensorTriangulated.smashSuspIso (Sphere k) X ≪≫
      (shiftFunctor C 1).mapIso ih ≪≫
      ((shiftFunctorAdd C k 1).app X).symm)
    (fun k _ ih =>
      have hk : k - 1 = k + (-1) := by omega
      hk ▸
      (((tensorRight X).mapIso ((shiftFunctorAdd C k (-1)).app SphereSpectrum)) ≪≫
      smashDesuspIso (Sphere k) X ≪≫
      (shiftFunctor C (-1 : ℤ)).mapIso ih ≪≫
      ((shiftFunctorAdd C k (-1)).app X).symm))

/-- The mapping spectrum is represented by the internal hom. -/
noncomputable def mappingSpectrumHomotopy (n : ℤ) (X Y : C) :
    HomotopyGroup n (MappingSpectrum X Y) ≃
      ((shiftFunctor C n).obj X ⟶ Y) :=
  ((ihom.adjunction X).homEquiv (Sphere n) Y).symm |>.trans
    (Iso.homCongr ((β_ X (Sphere n)).trans (sphere_tensor_shift n X))
      (Iso.refl Y))

end KIP126.StableHomotopy
