import KIP126.Def.SpectralSequence.BoundedExtension.BoundedComplex.Data
import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
import KIP126.Def.SpectralSequence.Convergence.SSData.Category.Data

/-!
# The bounded self complex of a convergent spectral sequence
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω' : Type w}
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- At a fixed stem, the identity of the target of a convergent spectral
sequence regarded as a bounded two-term filtered complex. -/
noncomputable def selfComplex
    (X : ConvergingSS C ω ω') (hb : X.F.IsBounded) (t : ω') :
    BoundedFilteredComplex C :=
  ⟨underlyingComplex (fun k' => 𝟙 (X.A k'))
      (fun s k' => X.F.fcId s k') t,
    underlyingComplexBounded (F₁ := X.F) (F₂ := X.F)
      (fun k' => 𝟙 (X.A k')) (fun s k' => X.F.fcId s k') t hb hb⟩

end KIP126.Core.SpectralSequence
