import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.CategoryTheory.Localization.Construction

/-!
Concrete sequential prespectra and their stable homotopy category.

A structure map is written as `I × X_n → X_(n+1)`, constant on the
ends and on `I × {*}`. This is exactly a based map `Σ X_n → X_(n+1)`.
Stable weak equivalences are defined using cubical representatives of
stable homotopy groups, not supplied as an unspecified predicate.
-/

noncomputable section
open CategoryTheory
open scoped unitInterval Topology

namespace KervaireChallenge

structure Spectrum where
  space : ℕ → Type
  topology : ∀ n, TopologicalSpace (space n)
  point : ∀ n, space n
  bond : ∀ n, @ContinuousMap (I × space n) (space (n + 1))
    (instTopologicalSpaceProd) (topology (n + 1))
  bond_zero : ∀ n x, bond n (0, x) = point (n + 1)
  bond_one : ∀ n x, bond n (1, x) = point (n + 1)
  bond_point : ∀ n t, bond n (t, point n) = point (n + 1)

attribute [instance] Spectrum.topology

namespace Spectrum

structure Map (X Y : Spectrum) where
  app : ∀ n, C(X.space n, Y.space n)
  point : ∀ n, app n (X.point n) = Y.point n
  bond : ∀ n t x, app (n + 1) (X.bond n (t, x)) =
    Y.bond n (t, app n x)

@[ext] theorem Map.ext {X Y : Spectrum} {f g : Map X Y}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g; congr; exact funext h

instance : Category Spectrum where
  Hom := Map
  id X := ⟨fun _ => ContinuousMap.id _, fun _ => rfl, fun _ _ _ => rfl⟩
  comp f g := ⟨fun n => (g.app n).comp (f.app n),
    fun n => by simp [f.point, g.point],
    fun n t x => by simp [ContinuousMap.comp_apply, f.bond, g.bond]⟩
  id_comp f := by ext n x; rfl
  comp_id f := by ext n x; rfl
  assoc f g h := by ext n x; rfl

abbrev Loop (X : Spectrum) (level dim : ℕ) : Type :=
  ↥(GenLoop (Fin dim) (X.space level) (X.point level))

/-- Suspension of a cubical representative, followed by the spectrum structure map. -/
def suspendLoop (X : Spectrum) {level dim : ℕ} (f : X.Loop level dim) :
    X.Loop (level + 1) (dim + 1) := by
  refine ⟨⟨fun u => X.bond level (u 0, f.1 (fun i => u i.succ)), ?_⟩, ?_⟩
  · exact (X.bond level).continuous.comp
      ((continuous_apply 0).prodMk (f.1.continuous.comp
        (continuous_pi fun i => continuous_apply i.succ)))
  · intro u hu
    change X.bond level (u 0, f.1 (fun i => u i.succ)) = _
    obtain ⟨i, hi⟩ := hu
    refine Fin.cases ?_ (fun j => ?_) i hi
    · intro hi
      rcases hi with hi | hi
      · simp [hi, X.bond_zero]
      · simp [hi, X.bond_one]
    · intro hi
      rw [f.2 (fun i => u i.succ) ⟨j, hi⟩, X.bond_point]

/-- Representatives in all stable degrees. The degree is `dim - level`. -/
structure Representative (X : Spectrum) where
  level : ℕ
  dim : ℕ
  loop : X.Loop level dim

inductive StableStep (X : Spectrum) : X.Representative → X.Representative → Prop
  | homotopy {level dim} (f g : X.Loop level dim) (h : GenLoop.Homotopic f g) :
      StableStep X ⟨level, dim, f⟩ ⟨level, dim, g⟩
  | suspension {level dim} (f : X.Loop level dim) :
      StableStep X ⟨level, dim, f⟩ ⟨level + 1, dim + 1, X.suspendLoop f⟩

/-- Equality after finitely many suspensions and based homotopies. -/
def StablyHomotopic (X : Spectrum) : X.Representative → X.Representative → Prop :=
  Relation.EqvGen X.StableStep

def mapLoop {X Y : Spectrum} (f : X ⟶ Y) {level dim} (a : X.Loop level dim) :
    Y.Loop level dim :=
  ⟨(f.app level).comp a.1, fun u hu => by
    change f.app level (a.1 u) = Y.point level
    rw [a.2 u hu, f.point]⟩

def mapRepresentative {X Y : Spectrum} (f : X ⟶ Y) (a : X.Representative) :
    Y.Representative := ⟨a.level, a.dim, mapLoop f a.loop⟩

/-- A map is a stable equivalence iff it induces bijections on all stable
homotopy groups. Using all representatives at once includes negative degrees. -/
def stableEquivalences : MorphismProperty Spectrum := fun X Y f =>
  (∀ b : Y.Representative, ∃ a : X.Representative,
    Y.StablyHomotopic (mapRepresentative f a) b) ∧
  (∀ a b : X.Representative,
    Y.StablyHomotopic (mapRepresentative f a) (mapRepresentative f b) →
      X.StablyHomotopic a b)

end Spectrum

/-- The actual stable homotopy category: prespectra localized at π_*-isomorphisms. -/
abbrev StableCategory := Spectrum.stableEquivalences.Localization

abbrev toStable : Spectrum ⥤ StableCategory := Spectrum.stableEquivalences.Q

end KervaireChallenge
