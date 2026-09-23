import KIP126.Def.SpectralSequence.Crossing.Data
import KIP126.Def.SpectralSequence.Convergence.SSData.Data

/-! Differential relations and crossing predicates for the `SSData` model. -/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- The differential at `(r,k)` is essential when it is nonzero. -/
def IsEssentialAt (E : SpectralSequence C ι) (r : ℤ) (k : ι) : Prop :=
  E.d r k ≠ 0

/-- Relation on ambient representatives induced by `d_r`. -/
def DifferentialRelation
    (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V) : Prop :=
  let n : WithTop ℕ := ↑(r - E.r₀).toNat
  ∃ (xZ : T ⟶ Subobject.underlying.obj ((E.ssData k).Z n)),
    xZ ≫ ((E.ssData k).Z n).arrow = x ∧
      ∃ (yZ : T ⟶ Subobject.underlying.obj
        ((E.ssData (k + E.diffDeg r)).Z n)),
        yZ ≫ ((E.ssData (k + E.diffDeg r)).Z n).arrow = y ∧
          xZ ≫ (E.ssData k).pageπ n ≫ E.d r k =
            yZ ≫ (E.ssData (k + E.diffDeg r)).pageπ n

/-- A differential relation whose target representative is not a boundary. -/
def EssentialDifferentialRelation
    (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V) : Prop :=
  DifferentialRelation E r k x y ∧
    ¬ Subobject.Factors
      ((E.ssData (k + E.diffDeg r)).B
        (↑(r - E.r₀).toNat : WithTop ℕ)) y

/-- An ambient representative and the page class it represents. -/
def ElementPageRel
    (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (a : T ⟶ (E.ssData k).page
      (↑(r - E.r₀).toNat : WithTop ℕ)) : Prop :=
  ∃ (xZ : T ⟶ Subobject.underlying.obj
      ((E.ssData k).Z (↑(r - E.r₀).toNat : WithTop ℕ))),
    xZ ≫ ((E.ssData k).Z
      (↑(r - E.r₀).toNat : WithTop ℕ)).arrow = x ∧
      xZ ≫ (E.ssData k).pageπ
        (↑(r - E.r₀).toNat : WithTop ℕ) = a

/-- A relation crossed by an essential relation from higher filtration. -/
def RelationCrossedBy
    (E : SpectralSequence C ι) (filtDeg : ι → ℤ) (r : ℤ) (k : ι)
    {T : C} (x : T ⟶ (E.ssData k).V)
    (y : T ⟶ (E.ssData (k + E.diffDeg r)).V)
    (_h : DifferentialRelation E r k x y) : Prop :=
  ∃ (a : ℤ) (_ : 0 < a) (m : ℤ) (k' : ι)
    (x' : T ⟶ (E.ssData k').V)
    (y' : T ⟶ (E.ssData (k' + E.diffDeg m)).V),
    filtDeg k' = filtDeg k + a ∧
      EssentialDifferentialRelation E m k' x' y' ∧
      filtDeg (k' + E.diffDeg m) ≤ filtDeg k + r

/-- A crossing whose target filtration is `p`. -/
def HasCrossingAt (dd : DifferentialDatum C ι) (p : ℤ) : Prop :=
  let s := dd.filtDeg dd.k
  ∃ (a : ℤ) (_ : 0 < a) (m : ℤ) (k' : ι),
    dd.filtDeg k' = s + a ∧
      IsEssentialAt dd.E m k' ∧
      p = s + a + m ∧
      s + a + m ≤ s + dd.r

/-- No essential crossing lands in the indicated filtration range. -/
def NoCrossingRange (dd : DifferentialDatum C ι) (p : ℤ) : Prop :=
  ¬ ∃ (a : ℤ) (_ : 0 < a) (m : ℤ) (k' : ι),
    dd.filtDeg k' = dd.filtDeg dd.k + a ∧
      IsEssentialAt dd.E m k' ∧
      p ≤ dd.filtDeg dd.k + a + m ∧
      dd.filtDeg dd.k + a + m ≤ dd.filtDeg dd.k + dd.r

/-- The selected differential has no crossing. -/
def NoCrossing (dd : DifferentialDatum C ι) : Prop :=
  NoCrossingRange dd (dd.filtDeg dd.k + 1)

/-- Crossing predicate relative to supplied convergence data. -/
def HasCrossingAt_conv
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (_conv : Convergence E A F) (dd : DifferentialDatum C ω) (p : ℤ) : Prop :=
  HasCrossingAt dd p

end KIP126.Core.SpectralSequence
