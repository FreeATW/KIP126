import KIP126.Def.StableHomotopy.Context.MappingProofs

/-! Regression checks for sphere-smash and mapping-spectrum interfaces. -/
namespace KIP126.Checks.StableHomotopy

open CategoryTheory MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [ClosedSymmetricTensorTriangulated (C := C)]

example (n : ℤ) (X : C) :
    Nonempty ((Sphere n : C) ⊗ X ≅ (shiftFunctor C n).obj X) :=
  ⟨sphere_tensor_shift n X⟩

example (n : ℤ) (X Y : C) :
    Nonempty
      (HomotopyGroup n (MappingSpectrum X Y) ≃
        ((shiftFunctor C n).obj X ⟶ Y)) :=
  ⟨mappingSpectrumHomotopy n X Y⟩

end KIP126.Checks.StableHomotopy
