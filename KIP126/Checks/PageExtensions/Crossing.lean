import KIP126.Def.PageExtensions.Proofs

/-! Regression checks for the page-level crossing interface. -/

namespace KIP126.Checks.PageExtensions

open CategoryTheory
open KIP126.Def.PageExtensions

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable {E : KIP126.Def.PageExtensions.SpectralSequence C c r₀}

#check DifferentialRelation
#check EssentialDifferentialRelation
#check RelationCrossedBy
#check DifferentialDatum.ofSpectralSequence
#check not_hasCrossingAt_of_noCrossing

end KIP126.Checks.PageExtensions
