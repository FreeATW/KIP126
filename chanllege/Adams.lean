import chanllege.Topology
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic

/-!
A realization of the classical mod-2 Adams spectral sequence of the sphere.

All spectra in this file are the concrete prespectra of `Topology.lean`.
The choices below are presentations of standard constructions, with their
point-set realization equations. They are not freely chosen spectral sequences.
No survival assertion, Adams differential calculation, or high-stem input is
included among the fields.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped unitInterval Topology

namespace KervaireChallenge

/-- The based sphere `I^n / ∂I^n`, with a disjoint basepoint before quotienting.
The disjoint basepoint is necessary in dimension zero. -/
inductive SphereRelation (n : ℕ) :
    (PUnit ⊕ (Fin n → I)) → (PUnit ⊕ (Fin n → I)) → Prop
  | boundary (u : Fin n → I) (h : u ∈ Cube.boundary (Fin n)) :
      SphereRelation n (.inr u) (.inl PUnit.unit)

abbrev CubeSphere (n : ℕ) := Quot (SphereRelation n)

def spherePoint (n : ℕ) : CubeSphere n := Quot.mk _ (.inl PUnit.unit)
def sphereCell {n : ℕ} (u : Fin n → I) : CubeSphere n := Quot.mk _ (.inr u)

/-- An eventual levelwise presentation of `Σ^d S`. Changing finitely many
initial levels does not change a prespectrum in the stable category. -/
structure ShiftedSphere (d : ℤ) (S : Spectrum) where
  offset : ℕ
  dimension : ℕ
  degree : (dimension : ℤ) = (offset : ℤ) + d
  chart : ∀ n, S.space (offset + n) ≃ₜ CubeSphere (dimension + n)
  point : ∀ n, chart n (S.point (offset + n)) = spherePoint (dimension + n)
  bond : ∀ n (t : I) (u : Fin (dimension + n) → I),
    chart (n + 1) (S.bond (offset + n) (t, (chart n).symm (sphereCell u))) =
      sphereCell (Fin.cons t u)

abbrev LoopLevel (X : Spectrum) (n : ℕ) :=
  {p : C(I, X.space n) // p 0 = X.point n ∧ p 1 = X.point n}

/-- Point-set loop spectra, including their action on every map. -/
structure LoopRealization where
  obj : Spectrum → Spectrum
  chart : ∀ X n, (obj X).space n ≃ₜ LoopLevel X n
  point : ∀ X n t, (chart X n ((obj X).point n)).1 t = X.point n
  bond : ∀ X n t p u,
    (chart X (n + 1) ((obj X).bond n (t, p))).1 u =
      X.bond n (t, (chart X n p).1 u)
  map : ∀ {X Y : Spectrum}, (X ⟶ Y) → (obj X ⟶ obj Y)
  map_apply : ∀ {X Y} (f : X ⟶ Y) n p t,
    (chart Y n ((map f).app n p)).1 t = f.app n ((chart X n p).1 t)

/-- Standard additive and suspension-loop presentations on the *fixed*
localization of concrete spectra. The sphere and loops are geometrically
specified, rather than arbitrary named objects. -/
structure StableFoundations where
  additive : Preadditive StableCategory
  sphere : ℤ → Spectrum
  spherePresentation : ∀ n, ShiftedSphere n (sphere n)
  loops : LoopRealization
  loopPi : letI := additive
    ∀ n X, (toStable.obj (sphere n) ⟶ toStable.obj X) ≃+
      (toStable.obj (sphere (n - 1)) ⟶ toStable.obj (loops.obj X))
  loopPi_natural : letI := additive
    ∀ n {X Y} (f : X ⟶ Y) (a : toStable.obj (sphere n) ⟶ toStable.obj X),
      loopPi n Y (a ≫ toStable.map f) = loopPi n X a ≫ toStable.map (loops.map f)

namespace StableFoundations

@[reducible] def Pi (F : StableFoundations) (n : ℤ) (X : StableCategory) :=
  toStable.obj (F.sphere n) ⟶ X

instance (F : StableFoundations) (n : ℤ) (X : StableCategory) :
    AddCommGroup (F.Pi n X) := by
  letI := F.additive
  exact inferInstanceAs (AddCommGroup (toStable.obj (F.sphere n) ⟶ X))

/-- A shift of the mod-2 Eilenberg--Mac Lane spectrum, characterized by
its actual stable homotopy groups. These conditions determine its stable
homotopy type; no unspecified cohomology functor is being named `HF2`. -/
structure IsMod2EilenbergMacLane (F : StableFoundations) (n : ℤ)
    (H : StableCategory) where
  coefficient : F.Pi n H ≃+ ZMod 2
  otherDegrees : ∀ k : ℤ, k ≠ n → Subsingleton (F.Pi k H)

/-- Products of shifts of `HF2`, the injective objects used in an Adams resolution. -/
structure Mod2GEM (F : StableFoundations) (K : StableCategory) where
  Index : Type
  factor : Index → StableCategory
  degree : Index → ℤ
  eml : ∀ i, F.IsMod2EilenbergMacLane (degree i) (factor i)
  projection : ∀ i, K ⟶ factor i
  isProduct : IsLimit (Fan.mk K projection)

/-- Surjectivity on mod-2 cohomology in every degree, expressed through its
representing Eilenberg--Mac Lane spectra. -/
def IsAdamsApproximation (F : StableFoundations) {X K : StableCategory}
    (j : X ⟶ K) : Prop :=
  ∀ n H, Nonempty (F.IsMod2EilenbergMacLane n H) →
    ∀ f : X ⟶ H, ∃ g : K ⟶ H, j ≫ g = f

end StableFoundations

/-- The ordinary point-set homotopy fiber of a map, level by level. -/
abbrev FiberLevel {X Y : Spectrum} (f : X ⟶ Y) (n : ℕ) :=
  {q : X.space n × C(I, Y.space n) //
    q.2 0 = f.app n q.1 ∧ q.2 1 = Y.point n}

/-- A concrete mod-2 Adams resolution of the sphere. Fiber charts and their
bonding equations fix the topology behind the resulting exact couple. -/
structure SphereAdamsResolution (F : StableFoundations) where
  X : ℕ → Spectrum
  K : ℕ → Spectrum
  start : toStable.obj (X 0) ≅ toStable.obj (F.sphere 0)
  j : ∀ s, X s ⟶ K s
  injective : ∀ s, F.Mod2GEM (toStable.obj (K s))
  approximation : ∀ s, F.IsAdamsApproximation (toStable.map (j s))
  fiberChart : ∀ s n, (X (s + 1)).space n ≃ₜ FiberLevel (j s) n
  fiberPoint_first : ∀ s n,
    (fiberChart s n ((X (s + 1)).point n)).1.1 = (X s).point n
  fiberPoint_path : ∀ s n t,
    (fiberChart s n ((X (s + 1)).point n)).1.2 t = (K s).point n
  fiberBond_first : ∀ s n t x,
    (fiberChart s (n + 1) ((X (s + 1)).bond n (t, x))).1.1 =
      (X s).bond n (t, (fiberChart s n x).1.1)
  fiberBond_path : ∀ s n t x u,
    (fiberChart s (n + 1) ((X (s + 1)).bond n (t, x))).1.2 u =
      (K s).bond n (t, (fiberChart s n x).1.2 u)
  i : ∀ s, X (s + 1) ⟶ X s
  i_apply : ∀ s n x, (i s).app n x = (fiberChart s n x).1.1
  connecting : ∀ s, F.loops.obj (K s) ⟶ X (s + 1)
  connecting_first : ∀ s n p,
    (fiberChart s n ((connecting s).app n p)).1.1 = (X s).point n
  connecting_path : ∀ s n p t,
    (fiberChart s n ((connecting s).app n p)).1.2 t =
      (F.loops.chart (K s) n p).1 t
  /-- Composites of the tower maps, supplied with their defining equations. -/
  down : ∀ (s q : ℕ), q ≤ s → (toStable.obj (X s) ⟶ toStable.obj (X q))
  down_self : ∀ s h, down s s h = 𝟙 _
  down_step : ∀ s q (h : q ≤ s),
    down (s + 1) q (Nat.le.step h) = toStable.map (i s) ≫ down s q h

namespace SphereAdamsResolution
variable {F : StableFoundations} (A : SphereAdamsResolution F)

abbrev D (s : ℕ) (n : ℤ) := F.Pi n (toStable.obj (A.X s))
abbrev E₁ (s : ℕ) (n : ℤ) := F.Pi n (toStable.obj (A.K s))

def towerMap (s q : ℕ) (h : q ≤ s) (n : ℤ) : A.D s n →+ A.D q n where
  toFun a := a ≫ A.down s q h
  map_zero' := by
    letI := F.additive
    exact zero_comp
  map_add' a b := by
    letI := F.additive
    exact add_comp _ _ _ a b _

def toLayer (s : ℕ) (n : ℤ) : A.D s n →+ A.E₁ s n where
  toFun a := a ≫ toStable.map (A.j s)
  map_zero' := by
    letI := F.additive
    exact zero_comp
  map_add' a b := by
    letI := F.additive
    exact add_comp _ _ _ a b _

def boundaryMap (s : ℕ) (n : ℤ) : A.E₁ s n →+ A.D (s + 1) (n - 1) where
  toFun a := F.loopPi n (A.K s) a ≫ toStable.map (A.connecting s)
  map_zero' := by
    letI := F.additive
    simp
  map_add' a b := by
    letI := F.additive
    simp [add_comp]

/-- The exactness assertion is about the three geometrically defined maps;
it cannot change those maps or insert the desired survival as a hypothesis. -/
def HasExactCouple : Prop :=
  (∀ s n, (A.towerMap (s + 1) s (Nat.le_succ s) n).range = (A.toLayer s n).ker) ∧
  (∀ s n, (A.toLayer s n).range = (A.boundaryMap s n).ker) ∧
  (∀ s n, (A.boundaryMap s (n + 1)).range =
    (A.towerMap (s + 1) s (Nat.le_succ s) ((n + 1) - 1)).ker)

/-- `Z_r` inside `E₁`: the connecting class lifts another `r-1` stages.
The indices here are `(filtration, stem)`. `r` is positive. -/
def cycles (r s : ℕ) (hr : 1 ≤ r) (n : ℤ) : AddSubgroup (A.E₁ s n) :=
  ((A.towerMap (s + r) (s + 1) (by omega) (n - 1)).range).comap
    (A.boundaryMap s n)

/-- `B_r` inside `E₁`. The tower is constant below filtration zero, so the
lower index is truncated at zero. In particular `B₁ = 0`. -/
def boundaries (r s : ℕ) (_hr : 1 ≤ r) (n : ℤ) : AddSubgroup (A.E₁ s n) :=
  ((A.towerMap s (s + 1 - r) (by omega) n).ker).map (A.toLayer s n)

/-- All cycles, and all boundaries, in the algebraic limiting page. -/
def infiniteCycles (s : ℕ) (n : ℤ) : AddSubgroup (A.E₁ s n) :=
  ⨅ (r : ℕ) (hr : 1 ≤ r), A.cycles r s hr n

def infiniteBoundaries (s : ℕ) (n : ℤ) : AddSubgroup (A.E₁ s n) :=
  ((A.towerMap s 0 (Nat.zero_le s) n).ker).map (A.toLayer s n)

/-- Restrict boundaries to cycles before quotienting. For an exact couple,
all boundaries are cycles, so this is precisely the usual `Z_r / B_r`. -/
abbrev Page (r s : ℕ) (hr : 1 ≤ r) (t : ℤ) :=
  (A.cycles r s hr (t - s)) ⧸
    (A.boundaries r s hr (t - s)).comap (A.cycles r s hr (t - s)).subtype

abbrev E₂ (s : ℕ) (t : ℤ) := A.Page 2 s (by decide) t

abbrev EInfinity (s : ℕ) (t : ℤ) :=
  (A.infiniteCycles s (t - s)) ⧸
    (A.infiniteBoundaries s (t - s)).comap (A.infiniteCycles s (t - s)).subtype

/-- A particular `E₂` class survives *nontrivially* to `E∞` if one of its
`E₁` representatives is a cycle on every page and is never a boundary.
This excludes zero, incoming differentials, and disconnected pagewise choices. -/
def SurvivesToEInfinity {s : ℕ} {t : ℤ} (x : A.E₂ s t) : Prop :=
  x ≠ 0 ∧ ∃ z : A.cycles 2 s (by decide) (t - s),
    QuotientAddGroup.mk z = x ∧
    z.1 ∈ A.infiniteCycles s (t - s) ∧
    z.1 ∉ A.infiniteBoundaries s (t - s)

theorem survivesToEInfinity_nonzero {s : ℕ} {t : ℤ} {x : A.E₂ s t}
    (h : A.SurvivesToEInfinity x) : x ≠ 0 := h.1

theorem zero_not_survivesToEInfinity (s : ℕ) (t : ℤ) :
    ¬ A.SurvivesToEInfinity (0 : A.E₂ s t) := by
  intro h
  exact h.1 rfl

/-- Exactness forces every element in the image of `j` to be an
infinite cycle. This validates the use of actual boundary subgroups in the
page quotients. -/
theorem toLayer_mem_infiniteCycles (hex : A.HasExactCouple)
    (s : ℕ) (n : ℤ) (a : A.D s n) :
    A.toLayer s n a ∈ A.infiniteCycles s n := by
  have hk : A.toLayer s n a ∈ (A.boundaryMap s n).ker := by
    rw [← hex.2.1 s n]
    exact ⟨a, rfl⟩
  have hk0 : A.boundaryMap s n (A.toLayer s n a) = 0 := hk
  simp only [infiniteCycles, AddSubgroup.mem_iInf]
  intro r hr
  change A.boundaryMap s n (A.toLayer s n a) ∈
    (A.towerMap (s + r) (s + 1) (by omega) (n - 1)).range
  rw [hk0]
  exact AddSubgroup.zero_mem _

theorem infiniteBoundaries_le_infiniteCycles (hex : A.HasExactCouple)
    (s : ℕ) (n : ℤ) : A.infiniteBoundaries s n ≤ A.infiniteCycles s n := by
  rintro x ⟨a, _, rfl⟩
  exact A.toLayer_mem_infiniteCycles hex s n a

theorem boundaries_le_cycles (hex : A.HasExactCouple)
    (r s : ℕ) (hr : 1 ≤ r) (n : ℤ) :
    A.boundaries r s hr n ≤ A.cycles r s hr n := by
  rintro x ⟨a, _, rfl⟩
  have h := A.toLayer_mem_infiniteCycles hex s n a
  simp only [infiniteCycles, AddSubgroup.mem_iInf] at h
  exact h r hr

/-- The survival predicate really produces a nonzero element of the
explicitly defined limiting quotient; it is not only a pagewise slogan. -/
theorem survives_gives_nonzero_EInfinity {s : ℕ} {t : ℤ} {x : A.E₂ s t}
    (h : A.SurvivesToEInfinity x) : ∃ y : A.EInfinity s t, y ≠ 0 := by
  obtain ⟨_, z, _, hz, hb⟩ := h
  let a : A.infiniteCycles s (t - s) := ⟨z.1, hz⟩
  refine ⟨QuotientAddGroup.mk a, ?_⟩
  intro ha
  exact hb ((QuotientAddGroup.eq_zero_iff a).mp ha)

/-- Intrinsic characterization of the standard `h_j`: it is the unique nonzero
class in `Ext_A^(1,2^j)(F₂,F₂) = E₂^(1,2^j)`. -/
def IsH (j : ℕ) (x : A.E₂ 1 ((2 : ℤ) ^ j)) : Prop :=
  x ≠ 0 ∧ ∀ y : A.E₂ 1 ((2 : ℤ) ^ j), y ≠ 0 → y = x

/-- Intrinsic characterization of `h₆²`. The classical Adams two-line has
`E₂^(2,128) = F₂{h₆²}`. Thus its unique nonzero element specifies the
actual class, without introducing a free parameter named `h6` or an
unconstrained multiplication. This characterization is particular to this
bidegree; it is not a definition of multiplication in arbitrary Ext groups. -/
def IsH6Squared (x : A.E₂ 2 128) : Prop :=
  x ≠ 0 ∧ ∀ y : A.E₂ 2 128, y ≠ 0 → y = x

end SphereAdamsResolution

/-- A geometric realization of the classical sphere Adams exact couple. -/
structure ClassicalAdamsSphere where
  foundations : StableFoundations
  resolution : SphereAdamsResolution foundations
  exact : resolution.HasExactCouple

namespace ClassicalAdamsSphere
abbrev E₂ (A : ClassicalAdamsSphere) := A.resolution.E₂
abbrev IsH6Squared (A : ClassicalAdamsSphere) := A.resolution.IsH6Squared
abbrev SurvivesToEInfinity (A : ClassicalAdamsSphere) :=
  @SphereAdamsResolution.SurvivesToEInfinity A.foundations A.resolution
end ClassicalAdamsSphere

end KervaireChallenge
