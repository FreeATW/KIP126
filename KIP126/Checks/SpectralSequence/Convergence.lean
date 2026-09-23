import KIP126.Def.SpectralSequence.Convergence.Proofs
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Regression checks for endpoint-extended spectral sequences

These examples typecheck the public endpoint-extension interface without
postulating endpoint or convergence hypotheses.  In particular, they check
that an explicitly supplied `EndpointExtension` yields Mathlib's genuine
`E₂CohomologicalSpectralSequence`, while a `BoundaryWitness` supplies only the
stated limit/colimit comparisons.
-/

namespace KIP126.Core.SpectralSequence

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {FC : FilteredComplex C} (P : EndpointExtension FC)

section ConstructedZeroEndpoint

/-- A genuinely constructed endpoint-extension regression fixture.  All finite
filtration levels are zero subcomplexes of the zero complex, so the finite
comparison and both endpoint universal properties can be proved rather than
assumed as variables. -/
private noncomputable def zeroFilteredComplex : FilteredComplex C where
  complex := HomologicalComplex.zero
  filtration :=
    { F := fun _ _ => ⊥
      decreasing := by
        intro s k
        exact le_rfl }
  differential_preserves := by
    intro s k
    refine ⟨0, ?_⟩
    simp

private noncomputable def zeroFilteredChainIso (s : ℤ) :
    (zeroFilteredComplex (C := C)).filteredChainComplex s ≅ HomologicalComplex.zero := by
  refine HomologicalComplex.Hom.isoOfComponents (fun k => Subobject.botCoeIsoZero) ?_
  intro i j hij
  exact ((isZero_zero C).of_iso (Subobject.botCoeIsoZero)).eq_of_src _ _

private noncomputable def zeroFilteredCochainComplex : CochainComplex C ℤ :=
  (ChainComplex.cochainComplexEquivalence C).functor.obj HomologicalComplex.zero

private noncomputable def zeroFilteredCochainIso (s : ℤ) :
    (zeroFilteredComplex (C := C)).filteredCochainComplex s ≅
      zeroFilteredCochainComplex (C := C) :=
  (ChainComplex.cochainComplexEquivalence C).functor.mapIso
    (zeroFilteredChainIso (C := C) s)

private theorem zeroFilteredCochainIsZero (s : ℤ) :
    IsZero ((zeroFilteredComplex (C := C)).filteredCochainComplex s) :=
  (((ChainComplex.cochainComplexEquivalence C).functor.map_isZero
      (HomologicalComplex.isZero_zero (V := C) (c := ComplexShape.down ℤ))).of_iso
    (zeroFilteredCochainIso (C := C) s))

private theorem zeroFilteredCochainComplexIsZero :
    IsZero (zeroFilteredCochainComplex (C := C)) :=
  (ChainComplex.cochainComplexEquivalence C).functor.map_isZero
    (HomologicalComplex.isZero_zero (V := C) (c := ComplexShape.down ℤ))

private noncomputable def zeroFilteredFiniteIso :
    (zeroFilteredComplex (C := C)).filteredCochainDiagram ≅
      (Functor.const (OrderDual ℤ)).obj (zeroFilteredCochainComplex (C := C)) :=
  NatIso.ofComponents
    (fun s => zeroFilteredCochainIso (C := C) s)
    (by
      intro s t f
      exact (zeroFilteredCochainIsZero (C := C) s).eq_of_src _ _)

private noncomputable def zeroEndpointExtension :
    EndpointExtension (zeroFilteredComplex (C := C)) where
  diagram := (Functor.const EInt).obj (zeroFilteredCochainComplex (C := C))
  finiteIso := zeroFilteredFiniteIso (C := C)

private noncomputable def zeroEndpointBoundaryWitness :
    (zeroEndpointExtension (C := C)).BoundaryWitness where
  bottomIsLimit := IsLimit.ofIsZero _
    (Functor.isZero _ (fun _ => zeroFilteredCochainComplexIsZero (C := C)))
    (zeroFilteredCochainComplexIsZero (C := C))
  botIsZero := zeroFilteredCochainComplexIsZero (C := C)
  topIsColimit := IsColimit.ofIsZero _
    (Functor.isZero _ (fun _ => zeroFilteredCochainComplexIsZero (C := C)))
    (zeroFilteredCochainComplexIsZero (C := C))
  top := zeroFilteredCochainComplex (C := C)
  topIso := Iso.refl _

private noncomputable def zeroGradedObject : CategoryTheory.GradedObject ℤ C :=
  fun _ => HasZeroObject.zero.choose

private noncomputable def zeroFiltration : Algebra.Filtration (zeroGradedObject (C := C)) where
  F := fun _ _ => ⊥
  decreasing := by
    intro s i
    exact le_rfl

private theorem zeroFiltrationEventuallyZero :
    (zeroFiltration (C := C)).IsEventuallyZero := by
  intro i
  exact ⟨0, rfl⟩

example : EndpointExtension (zeroFilteredComplex (C := ModuleCat ℤ)) :=
  zeroEndpointExtension (C := ModuleCat ℤ)

example : (zeroEndpointExtension (C := ModuleCat ℤ)).BoundaryWitness :=
  zeroEndpointBoundaryWitness (C := ModuleCat ℤ)

example : IsLimit (zeroEndpointExtension (C := ModuleCat ℤ)).finiteBottomCone :=
  (zeroEndpointExtension (C := ModuleCat ℤ)).finiteBottomIsLimit
    (zeroEndpointBoundaryWitness (C := ModuleCat ℤ))

example : IsColimit (zeroEndpointExtension (C := ModuleCat ℤ)).finiteTopCocone :=
  (zeroEndpointExtension (C := ModuleCat ℤ)).finiteTopIsColimit
    (zeroEndpointBoundaryWitness (C := ModuleCat ℤ))

example (n : ℤ) :
    (zeroGradedObject (C := ModuleCat ℤ)) n ≅
      limit ((zeroFiltration (C := ModuleCat ℤ)).quotientTower n) := by
  let W := Algebra.Filtration.CompletionWitness.of_isEventuallyZero
    (zeroFiltration (C := ModuleCat ℤ))
    (zeroFiltrationEventuallyZero (C := ModuleCat ℤ)) n
  letI : HasLimit ((zeroFiltration (C := ModuleCat ℤ)).quotientTower n) := W.hasLimit
  exact W.completionIso

end ConstructedZeroEndpoint

section Endpoints

example : OrderDual ℤ ⥤ EInt :=
  decreasingFiltrationEmbedding

example : OrderDual ℤ ⥤ CochainComplex C ℤ :=
  P.finiteDiagram

example : Cone P.finiteDiagram :=
  P.bottomCone

example : Cocone P.finiteDiagram :=
  P.topCocone

example (W : P.BoundaryWitness) : IsLimit P.finiteBottomCone :=
  P.finiteBottomIsLimit W

example (W : P.BoundaryWitness) : IsColimit P.finiteTopCocone :=
  P.finiteTopIsColimit W

end Endpoints

section Morphisms

variable {GD GE : FilteredComplex C}
variable (Q : EndpointExtension GD) (R : EndpointExtension GE)
variable (f : FC ⟶ GD) (g : GD ⟶ GE)
variable (h : EndpointExtension.Hom P Q f)
variable (k : EndpointExtension.Hom Q R g)

example :
    EndpointExtension.Hom P P (FilteredComplex.Morphism.id FC) :=
  EndpointExtension.Hom.id P

example :
    EndpointExtension.Hom P R (FilteredComplex.Morphism.comp f g) :=
  EndpointExtension.Hom.comp h k

example :
    P.triangulatedSpectralObject ⟶ Q.triangulatedSpectralObject :=
  h.triangulatedSpectralObjectHom

variable {A : Type*} [Category A] [Abelian A]
variable (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
variable [F.ShiftSequence ℤ] [F.IsHomological]

example : P.abelianSpectralObject A F ⟶ Q.abelianSpectralObject A F :=
  h.abelianSpectralObjectHom A F

end Morphisms

section SpectralSequence

variable {A : Type*} [Category A] [Abelian A]
variable (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
variable [F.ShiftSequence ℤ] [F.IsHomological]

example :
    Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) EInt :=
  P.triangulatedSpectralObject

example : Abelian.SpectralObject A EInt :=
  P.abelianSpectralObject A F

example : CategoryTheory.E₂CohomologicalSpectralSequence A :=
  P.spectralSequence A F

example (p q : ℤ) :
    ((P.spectralSequence A F).page 2).X (p, q) ≅
      ((P.abelianSpectralObject A F).H (p + q)).obj
        (CategoryTheory.ComposableArrows.mk₁
          (homOfLE
            (Abelian.SpectralObject.coreE₂Cohomological.le₁₂ (p, q)))) :=
  P.firstPageXIso A F p q

end SpectralSequence

section PageAbutmentComparison

variable {A : Type*} [Category A] [Abelian A]
variable (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
variable [F.ShiftSequence ℤ] [F.IsHomological]
variable (W : PageAbutmentComparisonWitness P A F)

example : P.BoundaryWitness :=
  W.boundary

example : P.endpointAbutment A F ≅ W.abutment :=
  W.endpointAbutmentIso

example (n : ℤ) : Algebra.Filtration.CompletionWitness W.filtration n :=
  W.completion n

example (n : ℤ) : HasLimit (W.filtration.quotientTower n) :=
  (W.completion n).hasLimit

example : W.filtration.IsExhaustive :=
  W.exhaustive

example : W.filtration.IsEventuallyZero :=
  W.eventuallyZero

end PageAbutmentComparison

section StrongConvergence

variable {A : Type*} [Category A] [Abelian A]
variable (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
variable [F.ShiftSequence ℤ] [F.IsHomological]
variable (W : StrongConvergenceWitness P A F)

example : CategoryTheory.GradedObject (ℤ × ℤ) A :=
  W.eInfinity

example (pq : ℤ × ℤ) :
    W.eInfinity pq ≅ W.comparison.filtration.associatedGraded
      (W.comparison.filtrationDegree pq) (pq.1 + pq.2) :=
  W.eInfinityComparison pq

example (pq : ℤ × ℤ) (r : ℤ)
    (hr : W.comparison.comparisonPage pq ≤ r) :
    ((P.spectralSequence A F).page r
      ((W.comparison.comparisonPage_ge_two pq).trans hr)).X pq ≅
        W.comparison.filtration.associatedGraded
          (W.comparison.filtrationDegree pq) (pq.1 + pq.2) :=
  W.pageComparison pq r hr

example (pq : ℤ × ℤ) (r : ℤ)
    (hr : W.comparison.comparisonPage pq ≤ r) :
    (W.pageHomologyIso pq r hr).inv ≫
        ((P.spectralSequence A F).iso r (r + 1) pq rfl
          ((W.comparison.comparisonPage_ge_two pq).trans hr)).hom ≫
      (W.pageComparison pq (r + 1) (hr.trans (by omega))).hom =
        (W.pageComparison pq r hr).hom :=
  by simp

example (pq : ℤ × ℤ) :
    W.pageComparison pq (W.comparison.comparisonPage pq) le_rfl =
      W.comparison.pageComparison pq :=
  by simp

example (n : ℤ) :
    Algebra.Filtration.CompletionWitness W.comparison.filtration n :=
  W.comparison.completion n

example : W.comparison.filtration.IsExhaustive :=
  W.comparison.exhaustive

example : W.comparison.filtration.IsEventuallyZero :=
  W.comparison.eventuallyZero

example {T : A} {pq : ℤ × ℤ}
    (x : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) :
    W.Detects (0 : T ⟶ W.eInfinity pq) x ↔
      ∃ x' : T ⟶ Subobject.underlying.obj
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2)),
        x' ≫ Subobject.ofLE
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2))
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq) (pq.1 + pq.2))
          (W.comparison.filtration.decreasing
            (W.comparison.filtrationDegree pq) (pq.1 + pq.2)) = x :=
  W.detect_zero x

example {T : A} {pq : ℤ × ℤ}
    (y : T ⟶ W.eInfinity pq)
    (x x' : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) :
    (W.Detects y x ∧ W.Detects y x') ↔
      (W.Detects y x ∧
        ∃ z : T ⟶ Subobject.underlying.obj
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2)),
          z ≫ Subobject.ofLE
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2))
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq) (pq.1 + pq.2))
            (W.comparison.filtration.decreasing
              (W.comparison.filtrationDegree pq) (pq.1 + pq.2)) = x - x') :=
  W.detect_difference y x x'

end StrongConvergence

section ConcreteSpecialization

example {FC : FilteredComplex (ModuleCat ℤ)} (P : EndpointExtension FC) :
    CategoryTheory.E₂CohomologicalSpectralSequence (ModuleCat ℤ) :=
  P.spectralSequence (ModuleCat ℤ)
    (HomotopyCategory.homologyFunctor (ModuleCat ℤ)
      (ComplexShape.up ℤ) 0)

end ConcreteSpecialization

end

end KIP126.Core.SpectralSequence
