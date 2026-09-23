import KIP126.Def.ClassicalAdams.TowerSequence.NextHomology.Data

/-!
# Next-page boundaries vanish in current homology
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Express the incoming boundary map using the specified differential degree. -/
theorem adamsModuleCatBoundary_iff (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : LinearMap.ker ((adamsPageComplex unit X r hr).sc (s + r, t + r - 1)).g.hom) :
    x ∈ LinearMap.range ((adamsPageComplex unit X r hr).sc
      (s + r, t + r - 1)).moduleCatToCycles ↔
      ∃ y : adamsPage unit X r hr s t,
        adamsDifferential unit X r hr s t y = x.val := by
  have hp : (classicalAdamsShape r).prev (s + r, t + r - 1) = (s, t) := by
    apply ComplexShape.prev_eq'
    change (s, t) + ((r : ℤ), (r : ℤ) - 1) = _
    apply Prod.ext <;> dsimp
    omega
  simp only [LinearMap.mem_range, Subtype.ext_iff]
  change (∃ y : adamsPageObject unit X r hr
    ((classicalAdamsShape r).prev (s + r, t + r - 1)),
    (adamsPageD unit X r hr ((classicalAdamsShape r).prev (s + r, t + r - 1))
      (s + r, t + r - 1)).hom y = x.val) ↔ _
  rw [hp, adamsPageD_target]
  rfl

/-- A representative of a next-page boundary is hit by the current differential. -/
theorem adamsNextBoundary_is_differential (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X (r + 1) (Nat.succ_pos r) (s + r) (t + r - 1))
    (hx : x.val ∈ adamsBoundaries unit X (r + 1) (Nat.succ_pos r) (s + r) (t + r - 1)) :
    ∃ y : adamsPage unit X r hr s t,
      adamsDifferential unit X r hr s t y =
        adamsNextCycleToPage unit X r hr (s + r) (t + r - 1) x := by
  obtain ⟨z, hz, hj⟩ := hx
  change adamsI unit X ((t + r - 1) - (s + r))
    (s + r - (r + 1 : ℕ) + 1) (s + r) (by omega) z = 0 at hz
  have hs : s + r - (r + 1 : ℕ) + 1 = s := by omega
  have hz := (adamsI_image_zero_iff unit X _ _ _ _ hs (by omega) _).mp hz
  have e : (t + r - 1) - (s + r) = t - s - 1 := by omega
  let z' : HomotopyGroup (t - s - 1) (adamsTowerAt unit X (s + r)) :=
    Eq.mp (congrArg (fun n => HomotopyGroup n (adamsTowerAt unit X (s + r))) e) z
  have hz' : adamsI unit X (t - s - 1) s (s + r) (by omega) z' = 0 := by
    dsimp only [z']
    rw [adamsI_cast unit X e, hz, homotopyGroup_cast_zero e]
  obtain ⟨y, hy⟩ := adamsCycle_of_lift unit X r hr s t z' hz'
  refine ⟨(adamsCycleBoundaries unit X r hr s t).mkQ y, ?_⟩
  rw [adamsDifferential_mk, adamsDifferentialValue_eq_of_lift unit X r hr s t y z' hy.symm]
  dsimp only [z']
  rw [homotopyGroup_cast_cast (by omega) (by omega)]
  apply congrArg (adamsCycleBoundaries unit X r hr (s + r) (t + r - 1)).mkQ
  exact Subtype.ext hj

/-- Next-page boundaries become current-page homology boundaries. -/
theorem adamsNextBoundaries_le_ker (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    adamsCycleBoundaries unit X (r + 1) (Nat.succ_pos r) p.1 p.2 ≤
      LinearMap.ker (adamsNextCycleToHomology unit X r hr p) := by
  rintro x hx
  change adamsNextCycleToHomology unit X r hr p x = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  obtain ⟨s, t, rfl⟩ : ∃ s t : ℤ, p = (s + r, t + r - 1) := by
    refine ⟨p.1 - r, p.2 - r + 1, ?_⟩
    apply Prod.ext <;> dsimp <;> omega
  apply (adamsModuleCatBoundary_iff unit X r hr s t _).mpr
  exact adamsNextBoundary_is_differential unit X r hr s t x hx

/-- Precisely the next-page boundaries disappear in the current homology. -/
theorem adamsNextCycleToHomology_eq_zero_iff (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (x : adamsCycles unit X (r + 1) (Nat.succ_pos r) p.1 p.2) :
    adamsNextCycleToHomology unit X r hr p x = 0 ↔
      x ∈ adamsCycleBoundaries unit X (r + 1) (Nat.succ_pos r) p.1 p.2 := by
  constructor
  · intro h
    have hb := (Submodule.Quotient.mk_eq_zero _).mp h
    obtain ⟨s, t, rfl⟩ : ∃ s t : ℤ, p = (s + r, t + r - 1) := by
      refine ⟨p.1 - r, p.2 - r + 1, ?_⟩
      apply Prod.ext <;> dsimp <;> omega
    obtain ⟨y, hy⟩ := (adamsModuleCatBoundary_iff unit X r hr s t _).mp hb
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      have he : adamsJ unit X (s + r) (t + r - 1)
          (adamsDifferentialLift unit X r hr s t y) - x.val ∈
          adamsBoundaries unit X r hr (s + r) (t + r - 1) :=
        (Submodule.Quotient.eq (adamsCycleBoundaries unit X r hr (s + r) (t + r - 1))).mp hy
      have hm := (adamsBoundaries unit X (r + 1) (Nat.succ_pos r) (s + r) (t + r - 1)).sub_mem
        (adamsDifferentialLift_boundary unit X r hr s t y)
        (adamsBoundaries_le_succ unit X r hr (s + r) (t + r - 1) he)
      change x.val ∈ adamsBoundaries unit X (r + 1) (Nat.succ_pos r) (s + r) (t + r - 1)
      simpa only [sub_sub_cancel] using hm
  · exact fun hx => adamsNextBoundaries_le_ker unit X r hr p hx

end

end KIP126.Classical.Adams
