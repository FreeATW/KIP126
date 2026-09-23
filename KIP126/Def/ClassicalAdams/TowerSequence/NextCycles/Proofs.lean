import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Data

/-!
# Next-page cycles have zero current differential
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

omit [HasFunctorialCofiber (C := C)] in
/-- Opposite degree transports cancel. -/
theorem homotopyGroup_cast_cast {n n' : ℤ} (e : n = n') (e' : n' = n)
    (A : C) (x : HomotopyGroup n A) :
    Eq.mp (congrArg (fun n => HomotopyGroup n A) e')
      (Eq.mp (congrArg (fun n => HomotopyGroup n A) e) x) = x := by
  subst n'
  rfl

/-- Reindexing the common codomain preserves equality of tower images. -/
theorem adamsI_image_eq_iff (n a b s t : ℤ) (hab : a = b)
    (has : a ≤ s) (hat : a ≤ t)
    (x : HomotopyGroup n (adamsTowerAt unit X s))
    (y : HomotopyGroup n (adamsTowerAt unit X t)) :
    adamsI unit X n a s has x = adamsI unit X n a t hat y ↔
      adamsI unit X n b s (by omega) x = adamsI unit X n b t (by omega) y := by
  subst b
  rfl

/-- Reindexing the codomain preserves vanishing of a tower image. -/
theorem adamsI_image_zero_iff (n a b s : ℤ) (hab : a = b) (has : a ≤ s)
    (x : HomotopyGroup n (adamsTowerAt unit X s)) :
    adamsI unit X n a s has x = 0 ↔ adamsI unit X n b s (by omega) x = 0 := by
  subst b
  rfl

/-- Reindexing a tower stage preserves liftability. -/
theorem adamsI_range_eq (n a s t : ℤ) (hst : s = t) (has : a ≤ s) :
    LinearMap.range (adamsI unit X n a s has) =
      LinearMap.range (adamsI unit X n a t (by omega)) := by
  subst t
  rfl

/-- One tower step followed by the layer quotient gives the zero class. -/
theorem adamsJToPage_I_zero (r : ℕ) (hr : 1 ≤ r) (s t a : ℤ)
    (ha : a = s + 1) (y : HomotopyGroup (t - s) (adamsTowerAt unit X a)) :
    adamsJToPage unit X r hr s t (adamsI unit X (t - s) s a (by omega) y) = 0 := by
  subst a
  have hj : adamsJ unit X s t (adamsI unit X (t - s) s (s + 1) (by omega) y) = 0 :=
    (les_homotopy_exact_f
      (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
      (t - s) _).mpr ⟨y, rfl⟩
  have hc : adamsJToCycles unit X r hr s t
      (adamsI unit X (t - s) s (s + 1) (by omega) y) = 0 := Subtype.ext hj
  change (adamsCycleBoundaries unit X r hr s t).mkQ _ = 0
  rw [hc, map_zero]

/-- Vanishing of a layer class is precisely liftability of its tower image
through the following stage. -/
theorem adamsJToPage_eq_zero_iff (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (y : HomotopyGroup (t - s) (adamsTowerAt unit X s)) :
    adamsJToPage unit X r hr s t y = 0 ↔
      ∃ z : HomotopyGroup (t - s) (adamsTowerAt unit X (s + 1)),
        adamsI unit X (t - s) (s - r + 1) (s + 1) (by omega) z =
          adamsI unit X (t - s) (s - r + 1) s (by omega) y := by
  constructor
  · intro h
    have hb : adamsJ unit X s t y ∈ adamsBoundaries unit X r hr s t :=
      (Submodule.Quotient.mk_eq_zero (adamsCycleBoundaries unit X r hr s t)).mp h
    obtain ⟨w, hw, hj⟩ := hb
    have he : adamsJ unit X s t (y - w) = 0 := by
      rw [map_sub, hj, sub_self]
    obtain ⟨z, hz⟩ := (les_homotopy_exact_f
      (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
      (t - s) (y - w)).mp he
    change adamsI unit X (t - s) s (s + 1) (by omega) z = y - w at hz
    refine ⟨z, ?_⟩
    rw [← adamsI_comp unit X (t - s) (s - r + 1) s (s + 1)
      (by omega) (by omega), hz, map_sub]
    change adamsI unit X (t - s) (s - r + 1) s (by omega) w = 0 at hw
    rw [hw, sub_zero]
  · rintro ⟨z, hz⟩
    rw [adamsJToPage_eq unit X r hr s t rfl y
      (adamsI unit X (t - s) s (s + 1) (by omega) z) (by
        rw [adamsI_comp, hz])]
    exact adamsJToPage_I_zero unit X r hr s t (s + 1) rfl z

/-- The representative calculation before converting to the complex's indexing. -/
theorem adamsNextCycle_differential_zero (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X (r + 1) (by omega) s t) :
    adamsDifferential unit X r hr s t (adamsNextCycleToPage unit X r hr s t x) = 0 := by
  let y := adamsCycleLift unit X (r + 1) (by omega) s t x
  let z := adamsI unit X (t - s - 1) (s + r) (s + (r + 1 : ℕ)) (by omega) y
  change adamsDifferentialValue unit X r hr s t
    (Submodule.inclusion (adamsCycles_succ_le unit X r hr s t) x) = 0
  rw [adamsDifferentialValue_eq_of_lift unit X r hr s t _ z (by
    dsimp only [z]
    rw [adamsI_comp]
    exact adamsCycleLift_spec unit X (r + 1) (by omega) s t x)]
  unfold z
  rw [← adamsI_cast unit X (by omega)]
  exact adamsJToPage_I_zero unit X r hr (s + r) (t + r - 1)
    (s + (r + 1 : ℕ)) (by omega) _

/-- The kernel of the current differential consists exactly of the
representatives that lift one stage farther. -/
theorem adamsDifferentialValue_eq_zero_iff (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    adamsDifferentialValue unit X r hr s t x = 0 ↔
      x.val ∈ adamsCycles unit X (r + 1) (by omega) s t := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (adamsJToPage_eq_zero_iff unit X r hr
      (s + r) (t + r - 1) (adamsDifferentialLift unit X r hr s t x)).mp h
    have e : (t + r - 1) - (s + r) = t - s - 1 := by omega
    let z' : HomotopyGroup (t - s - 1) (adamsTowerAt unit X ((s + r) + 1)) :=
      Eq.mp (congrArg (fun n => HomotopyGroup n
        (adamsTowerAt unit X ((s + r) + 1))) e) z
    have hz' : adamsI unit X (t - s - 1) (s + 1) ((s + r) + 1) (by omega) z' =
        adamsK unit X s t x := by
      have ha : s + r - r + 1 = s + 1 := by omega
      have hz := (adamsI_image_eq_iff unit X _ _ _ _ _ ha (by omega) (by omega) _ _).mp hz
      dsimp only [z']
      rw [adamsI_cast unit X e, hz]
      unfold adamsDifferentialLift
      rw [adamsI_cast unit X (by omega)]
      rw [homotopyGroup_cast_cast (by omega) (by omega)]
      exact adamsCycleLift_spec unit X r hr s t x
    change adamsK unit X s t x ∈ LinearMap.range _
    rw [← adamsI_range_eq unit X (t - s - 1) (s + 1) ((s + r) + 1)
      (s + (r + 1 : ℕ)) (by omega) (by omega)]
    exact ⟨z', hz'⟩
  · intro hx
    exact adamsNextCycle_differential_zero unit X r hr s t ⟨x.val, hx⟩

/-- A lift killed by the preceding tower map is the connecting image of
an `r`-cycle. This is the exact-couple calculation behind next-page boundaries. -/
theorem adamsCycle_of_lift (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (y : HomotopyGroup (t - s - 1) (adamsTowerAt unit X (s + r)))
    (hy : adamsI unit X (t - s - 1) s (s + r) (by omega) y = 0) :
    ∃ x : adamsCycles unit X r hr s t,
      adamsK unit X s t x = adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega) y := by
  let a := adamsI unit X (t - s - 1) (s + 1) (s + r) (by omega) y
  have ha : adamsI unit X (t - s - 1) s (s + 1) (by omega) a = 0 := by
    dsimp only [a]
    rw [adamsI_comp, hy]
  obtain ⟨x, hx⟩ := (lesHomotopyExactH
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (t - s) a).mp ha
  change adamsK unit X s t x = a at hx
  exact ⟨⟨x, ⟨y, hx.symm⟩⟩, hx⟩

/-- The representative of a differential is a boundary on the next page. -/
theorem adamsDifferentialLift_boundary (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X r hr s t) :
    adamsJ unit X (s + r) (t + r - 1) (adamsDifferentialLift unit X r hr s t x) ∈
      adamsBoundaries unit X (r + 1) (by omega) (s + r) (t + r - 1) := by
  refine ⟨adamsDifferentialLift unit X r hr s t x, ?_, rfl⟩
  change adamsI unit X ((t + r - 1) - (s + r))
    ((s + r) - (r + 1 : ℕ) + 1) (s + r) (by omega) _ = 0
  have hs : (s + r) - (r + 1 : ℕ) + 1 = s := by omega
  apply (adamsI_image_zero_iff unit X _ _ _ _ hs (by omega) _).mpr
  unfold adamsDifferentialLift
  rw [adamsI_cast unit X (by omega),
    ← adamsI_comp unit X (t - s - 1) s (s + 1) (s + r) (by omega) (by omega),
    adamsCycleLift_spec]
  have hk : adamsI unit X (t - s - 1) s (s + 1) (by omega)
      (adamsK unit X s t x) = 0 :=
    (lesHomotopyExactH
      (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
      (t - s) _).mpr ⟨x.val, rfl⟩
  rw [hk, homotopyGroup_cast_zero (by omega)]

/-- The current-page image of a next-page cycle is killed by the differential. -/
theorem adamsNextCycle_d_zero (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (x : adamsCycles unit X (r + 1) (by omega) p.1 p.2) :
    ((adamsPageComplex unit X r hr).sc p).g
      (adamsNextCycleToPage unit X r hr p.1 p.2 x) = 0 := by
  have hn : (classicalAdamsShape r).next p = (p.1 + r, p.2 + r - 1) := by
    apply ComplexShape.next_eq'
    change p + ((r : ℤ), (r : ℤ) - 1) = _
    apply Prod.ext <;> dsimp
    omega
  let a : adamsPageObject unit X r hr p := adamsNextCycleToPage unit X r hr p.1 p.2 x
  change (adamsPageD unit X r hr p ((classicalAdamsShape r).next p)).hom a = 0
  rw [hn, adamsPageD_target]
  exact adamsNextCycle_differential_zero unit X r hr p.1 p.2 x

end

end KIP126.Classical.Adams
