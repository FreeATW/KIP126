import KIP126.Def.SpectralSequence.Basic.Data

/-! Data carried by a differential in a nested-subobject spectral sequence. -/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- A differential together with the filtration degrees of its gradings. -/
structure DifferentialDatum
    (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- Underlying nested-subobject spectral sequence. -/
  E : SpectralSequence C ι
  /-- Page number. -/
  r : ℤ
  /-- Source grading. -/
  k : ι
  /-- Filtration degree at every grading. -/
  filtDeg : ι → ℤ
  /-- The selected differential is nonzero. -/
  is_essential : E.d r k ≠ 0

/-- Construct differential data from a spectral sequence and an essentiality proof. -/
def DifferentialDatum.ofSpectralSequence
    (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    (filtDeg : ι → ℤ) (hess : E.d r k ≠ 0) :
    DifferentialDatum C ι :=
  { E := E
    r := r
    k := k
    filtDeg := filtDeg
    is_essential := hess }

end KIP126.Core.SpectralSequence
