import KIPBase.multiplicativeSS.DGA
import KIPBase.multiplicativeSS.TodaBracket

namespace KIPBase.SpectralSequence

universe u v w

class MasseyProduct (A : Type u) [Ring A] {ι : Type v} [AddCancelMonoid ι] [DecidableEq ι]
    {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    (dDegree : ι → ι) (leibnizSign : ι → A)
    (D : DGA A 𝒜 dDegree leibnizSign)
    (masseyGrading : ι → ι → ι → ι)
    (masseySign : ι → ι → ι → A) where
  juggling_grading : ∀ j k l m : ι,
    masseyGrading j k l + m = j + masseyGrading k l m
  massey_sign : ∀ i j k : ι, masseySign i j k = 1 ∨ masseySign i j k = -1
  massey_sign_grading : ∀ i j k : ι, masseySign i j k ∈ 𝒜 0
  defining_degree : Function.Surjective dDegree
  cycle_sign : ∀ j k l : ι,
    masseySign j k l * leibnizSign j = -1
  juggling_sign_coherence : ∀ j k l m p : ι, dDegree p = j + k →
    masseySign j k l * masseySign k l m = -leibnizSign p
  relation : ∀ {i j k l : ι}, 𝒜 i → 𝒜 j → 𝒜 k → 𝒜 l → Prop
  relation_grading : ∀ {i j k l : ι} {x : 𝒜 i} {a : 𝒜 j} {b : 𝒜 k} {c : 𝒜 l},
    relation x a b c → i = masseyGrading j k l
  relation_iff : ∀ {i j k l : ι} (x : 𝒜 i) (a : 𝒜 j) (b : 𝒜 k) (c : 𝒜 l),
    relation x a b c ↔ D.d (a : A) = 0 ∧ D.d (b : A) = 0 ∧
      D.d (c : A) = 0 ∧ ∃ (p q : ι) (y : 𝒜 p) (z : 𝒜 q),
      dDegree p = j + k ∧ dDegree q = k + l ∧ i = p + l ∧ i = j + q ∧
      D.d (y : A) = (a : A) * b ∧ D.d (z : A) = (b : A) * c ∧
      (x : A) = (y : A) * c + masseySign j k l * ((a : A) * z)

namespace MasseyProduct

variable {A : Type u} [Ring A] {ι : Type v} [AddCancelMonoid ι] [DecidableEq ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ι → σ} [GradedRing 𝒜] {dDegree : ι → ι} {leibnizSign : ι → A}
variable {D : DGA A 𝒜 dDegree leibnizSign}
variable {masseyGrading : ι → ι → ι → ι} {masseySign : ι → ι → ι → A}

noncomputable def homologyRepresentative (D : DGA A 𝒜 dDegree leibnizSign) {i : ι}
    (x : D.HomologyAt i) : D.HomogeneousCycles i :=
  Quotient.out x

@[simp]
theorem class_homologyRepresentative (D : DGA A 𝒜 dDegree leibnizSign) {i : ι}
    (x : D.HomologyAt i) : D.homogeneousClassOf (homologyRepresentative D x) = x :=
  Quotient.out_eq x

theorem of_component_eq_of_mem (D : DGA A 𝒜 dDegree leibnizSign)
    {i : ι} {x : D.GradedHomology} (hx : x ∈ D.homologyGrading i) :
    DirectSum.of D.HomologyAt i (x i) = x := by
  rcases hx with ⟨a, rfl⟩
  ext q
  by_cases hqi : q = i
  · subst q
    simp
  · simp [hqi]

theorem directSum_of_cast {F : ι → Type*} [∀ i, AddCommMonoid (F i)]
    {i j : ι} (h : i = j) (x : F i) :
    DirectSum.of F i x = DirectSum.of F j (cast (congrArg F h) x) := by
  subst j
  rfl

theorem cast_neg_homogeneousCycle (D : DGA A 𝒜 dDegree leibnizSign)
    {i j : ι} (h : i = j) (a : D.HomogeneousCycles i) :
    cast (congrArg D.HomogeneousCycles h) (-a) =
      -(cast (congrArg D.HomogeneousCycles h) a) := by
  subst j
  rfl

noncomputable def homologyRelation (M : MasseyProduct A 𝒜 dDegree leibnizSign D
    masseyGrading masseySign)
    {i j k l : ι} {x a b c : D.GradedHomology}
    (_hx : x ∈ D.homologyGrading i) (_ha : a ∈ D.homologyGrading j)
    (_hb : b ∈ D.homologyGrading k) (_hc : c ∈ D.homologyGrading l) : Prop :=
  ∃ x' : D.HomogeneousCycles i,
    DirectSum.of D.HomologyAt i (D.homogeneousClassOf x') = x ∧
    M.relation x'.1 (homologyRepresentative D (a j)).1
      (homologyRepresentative D (b k)).1 (homologyRepresentative D (c l)).1

/-- Every chain-level Massey relation has closed inputs and output. -/
theorem relation_cycles
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {i j k l : ι} (x : 𝒜 i) (a : 𝒜 j) (b : 𝒜 k) (c : 𝒜 l)
    (h : M.relation x a b c) :
    D.d (x : A) = 0 ∧ D.d (a : A) = 0 ∧
      D.d (b : A) = 0 ∧ D.d (c : A) = 0 := by
  rw [M.relation_iff] at h
  rcases h with ⟨ha, hb, hc, p, q, y, z, _, _, _, _, hy, hz, hx⟩
  refine ⟨?_, ha, hb, hc⟩
  rw [hx, D.d.map_add, D.leibniz y.2, hc, hy]
  simp only [mul_zero, add_zero]
  rcases M.massey_sign j k l with hs | hs
  · rw [hs, one_mul, D.leibniz a.2, ha, hz]
    have hcycle := M.cycle_sign j k l
    rw [hs] at hcycle
    simp only [one_mul] at hcycle
    rw [hcycle]
    noncomm_ring
  · rw [hs, neg_one_mul, D.d.map_neg, D.leibniz a.2, ha, hz]
    have hcycle := M.cycle_sign j k l
    rw [hs] at hcycle
    have heps : leibnizSign j = 1 := by
      simpa only [neg_one_mul, neg_inj] using hcycle
    rw [heps]
    noncomm_ring

def homologySignCycle (M : MasseyProduct A 𝒜 dDegree leibnizSign D
    masseyGrading masseySign) (j k l : ι) : D.HomogeneousCycles 0 :=
  ⟨⟨masseySign j k l, M.massey_sign_grading j k l⟩, by
    change D.d (masseySign j k l) = 0
    rcases M.massey_sign j k l with h | h
    · rw [h, D.d_one]
    · rw [h, D.d.map_neg, D.d_one, neg_zero]⟩

def homologyJugglingSign (M : MasseyProduct A 𝒜 dDegree leibnizSign D
    masseyGrading masseySign) (_i j k l : ι) : D.GradedHomology :=
  DirectSum.of D.HomologyAt 0 (D.homogeneousClassOf (M.homologySignCycle j k l))

theorem boundary_of_class_eq_zero (M : MasseyProduct A 𝒜 dDegree leibnizSign D
    masseyGrading masseySign) {i : ι} (a : D.HomogeneousCycles i)
    (h : D.homogeneousClassOf a = 0) : D.HomogeneousBoundary i (a.1 : A) := by
  have hr := Quotient.exact h
  change D.HomogeneousBoundary i ((a.1 : A) - 0) at hr
  simpa using hr

theorem boundary_data (M : MasseyProduct A 𝒜 dDegree leibnizSign D
    masseyGrading masseySign) {i : ι} {a : A}
    (h : D.HomogeneousBoundary i a) :
    ∃ (p : ι) (y : 𝒜 p), dDegree p = i ∧ D.d (y : A) = a := by
  rcases h with h | ⟨p, y, hp, hy⟩
  · obtain ⟨p, hp⟩ := M.defining_degree i
    exact ⟨p, 0, hp, by simp [h]⟩
  · exact ⟨p, y, hp, hy.symm⟩

theorem class_eq_zero_of_boundary (M : MasseyProduct A 𝒜 dDegree leibnizSign D
    masseyGrading masseySign) {i p : ι} (a : D.HomogeneousCycles i) (y : 𝒜 p)
    (hp : dDegree p = i) (hy : D.d (y : A) = (a.1 : A)) :
    D.homogeneousClassOf a = 0 := by
  apply Quotient.sound
  change D.HomogeneousBoundary i ((a.1 : A) - 0)
  refine Or.inr ⟨p, y, hp, ?_⟩
  simp [hy]

theorem homologyJugglingSign_eq_one_or_neg_one
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    (i j k l : ι) :
    M.homologyJugglingSign i j k l = 1 ∨ M.homologyJugglingSign i j k l = -1 := by
  rcases M.massey_sign j k l with h | h
  · left
    unfold homologyJugglingSign
    have hs : M.homologySignCycle j k l = D.homogeneousOne := by
      apply Subtype.ext
      apply Subtype.ext
      exact h
    rw [hs]
    rfl
  · right
    unfold homologyJugglingSign
    have hs : M.homologySignCycle j k l = -D.homogeneousOne := by
      apply Subtype.ext
      apply Subtype.ext
      change (masseySign j k l : A) = -1
      exact h
    rw [hs]
    change DirectSum.of D.HomologyAt 0 (-D.homogeneousClassOf D.homogeneousOne) = -1
    rw [map_neg]
    rfl

theorem homology_composable
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {i j k l : ι} {x a b c : D.GradedHomology}
    {hx : x ∈ D.homologyGrading i} {ha : a ∈ D.homologyGrading j}
    {hb : b ∈ D.homologyGrading k} {hc : c ∈ D.homologyGrading l}
    (h : M.homologyRelation hx ha hb hc) : a * b = 0 ∧ b * c = 0 := by
  rcases h with ⟨x', _, hrel⟩
  let a' := homologyRepresentative D (a j)
  let b' := homologyRepresentative D (b k)
  let c' := homologyRepresentative D (c l)
  have ha' : DirectSum.of D.HomologyAt j (D.homogeneousClassOf a') = a := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D ha
  have hb' : DirectSum.of D.HomologyAt k (D.homogeneousClassOf b') = b := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D hb
  have hc' : DirectSum.of D.HomologyAt l (D.homogeneousClassOf c') = c := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D hc
  rw [← ha', ← hb', ← hc']
  rw [M.relation_iff] at hrel
  rcases hrel with ⟨_, _, _, p, q, y, z, hp, hq, _, _, hy, hz, _⟩
  constructor
  · rw [DirectSum.of_mul_of]
    have hzero := M.class_eq_zero_of_boundary (D.homogeneousCycleMul a' b') y hp hy
    change DirectSum.of D.HomologyAt (j + k)
      (D.homologyMul (D.homogeneousClassOf a') (D.homogeneousClassOf b')) = 0
    rw [D.homologyMul_classOf]
    rw [hzero]
    exact map_zero (DirectSum.of D.HomologyAt (j + k))
  · rw [DirectSum.of_mul_of]
    have hzero := M.class_eq_zero_of_boundary (D.homogeneousCycleMul b' c') z hq hz
    change DirectSum.of D.HomologyAt (k + l)
      (D.homologyMul (D.homogeneousClassOf b') (D.homogeneousClassOf c')) = 0
    rw [D.homologyMul_classOf]
    rw [hzero]
    exact map_zero (DirectSum.of D.HomologyAt (k + l))

theorem homology_grading
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {i j k l : ι} {x a b c : D.GradedHomology}
    {hx : x ∈ D.homologyGrading i} {ha : a ∈ D.homologyGrading j}
    {hb : b ∈ D.homologyGrading k} {hc : c ∈ D.homologyGrading l}
    (h : M.homologyRelation hx ha hb hc) : i = masseyGrading j k l := by
  rcases h with ⟨x', _, hrel⟩
  exact M.relation_grading hrel

theorem representative_of_mem
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {i : ι} {a : D.GradedHomology} (ha : a ∈ D.homologyGrading i) :
    ∃ a' : D.HomogeneousCycles i,
      DirectSum.of D.HomologyAt i (D.homogeneousClassOf a') = a := by
  rcases ha with ⟨q, rfl⟩
  rcases Quotient.exists_rep q with ⟨a', rfl⟩
  exact ⟨a', rfl⟩

theorem product_boundary_of_zero
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {j k : ι} (a : D.HomogeneousCycles j) (b : D.HomogeneousCycles k)
    (h : DirectSum.of D.HomologyAt j (D.homogeneousClassOf a) *
      DirectSum.of D.HomologyAt k (D.homogeneousClassOf b) = 0) :
    D.HomogeneousBoundary (j + k) ((a.1 : A) * b.1) := by
  have heval := congrArg (fun t : D.GradedHomology => t (j + k)) h
  have hzero : D.homogeneousClassOf (D.homogeneousCycleMul a b) = 0 := by
    rw [DirectSum.of_mul_of] at heval
    have h3 : GradedMonoid.GMul.mul (D.homogeneousClassOf a)
        (D.homogeneousClassOf b) = 0 := by
      simpa using heval
    exact D.homologyMul_classOf a b ▸ h3
  exact M.boundary_of_class_eq_zero (D.homogeneousCycleMul a b) hzero

theorem homology_exists_relation
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {j k l : ι} {a b c : D.GradedHomology}
    (ha : a ∈ D.homologyGrading j) (hb : b ∈ D.homologyGrading k)
    (hc : c ∈ D.homologyGrading l) (hab : a * b = 0) (hbc : b * c = 0) :
    ∃ x : D.GradedHomology, ∃ hx : x ∈ D.homologyGrading (masseyGrading j k l),
      M.homologyRelation hx ha hb hc := by
  let a' := homologyRepresentative D (a j)
  let b' := homologyRepresentative D (b k)
  let c' := homologyRepresentative D (c l)
  have ha' : DirectSum.of D.HomologyAt j (D.homogeneousClassOf a') = a := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D ha
  have hb' : DirectSum.of D.HomologyAt k (D.homogeneousClassOf b') = b := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D hb
  have hc' : DirectSum.of D.HomologyAt l (D.homogeneousClassOf c') = c := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D hc
  rw [← ha', ← hb'] at hab
  rw [← hb', ← hc'] at hbc
  obtain ⟨p, y, hp, hy⟩ := M.boundary_data (M.product_boundary_of_zero a' b' hab)
  obtain ⟨q, z, hq, hz⟩ := M.boundary_data (M.product_boundary_of_zero b' c' hbc)
  have hpq : p + l = j + q := by
    apply D.dDegree_injective
    rw [D.dDegree_left, D.dDegree_right, hp, hq, add_assoc]
  have hxmem : (y : A) * c'.1 + masseySign j k l * ((a'.1 : A) * z) ∈ 𝒜 (p + l) := by
    apply add_mem
    · exact SetLike.mul_mem_graded y.2 c'.1.2
    · have hs := SetLike.mul_mem_graded (M.massey_sign_grading j k l)
          (SetLike.mul_mem_graded a'.1.2 z.2)
      simpa [hpq] using hs
  let x' : 𝒜 (p + l) :=
    ⟨(y : A) * c'.1 + masseySign j k l * ((a'.1 : A) * z), hxmem⟩
  have hxd : D.d (x' : A) = 0 := by
    dsimp [x']
    rw [D.d.map_add, D.leibniz y.2, D.homogeneousCycle_d c', hy]
    simp only [mul_zero, add_zero]
    rcases M.massey_sign j k l with hs | hs
    · rw [hs, one_mul, D.leibniz a'.1.2, D.homogeneousCycle_d a', hz]
      have hcycle := M.cycle_sign j k l
      rw [hs] at hcycle
      simp only [one_mul] at hcycle
      rw [hcycle]
      noncomm_ring
    · rw [hs, neg_one_mul, D.d.map_neg, D.leibniz a'.1.2,
        D.homogeneousCycle_d a', hz]
      have hcycle := M.cycle_sign j k l
      rw [hs] at hcycle
      have heps : leibnizSign j = 1 := by
        simpa only [neg_one_mul, neg_inj] using hcycle
      rw [heps]
      noncomm_ring
  let xc : D.HomogeneousCycles (p + l) := ⟨x', hxd⟩
  have hrel : M.relation x' a'.1 b'.1 c'.1 := by
    rw [M.relation_iff]
    exact ⟨D.homogeneousCycle_d a', D.homogeneousCycle_d b',
      D.homogeneousCycle_d c', p, q, y, z, hp, hq, rfl, hpq, hy, hz, rfl⟩
  have hgrade : p + l = masseyGrading j k l := M.relation_grading hrel
  let x'' : D.HomogeneousCycles (masseyGrading j k l) :=
    cast (congrArg D.HomogeneousCycles hgrade) xc
  let x := DirectSum.of D.HomologyAt (masseyGrading j k l) (D.homogeneousClassOf x'')
  have hx : x ∈ D.homologyGrading (masseyGrading j k l) := ⟨_, rfl⟩
  refine ⟨x, hx, x'', rfl, ?_⟩
  rw [M.relation_iff]
  refine ⟨D.homogeneousCycle_d a', D.homogeneousCycle_d b',
    D.homogeneousCycle_d c', p, q, y, z, hp, hq, hgrade.symm,
    hgrade.symm.trans hpq, hy, hz, ?_⟩
  rw [D.coe_cast_homogeneousCycle]
  all_goals first | rfl | exact hgrade

theorem homology_indeterminacy_left
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {i j k l m : ι} {x a b c y : D.GradedHomology}
    {hx : x ∈ D.homologyGrading i} {ha : a ∈ D.homologyGrading j}
    {hb : b ∈ D.homologyGrading k} {hc : c ∈ D.homologyGrading l}
    (hrelH : M.homologyRelation hx ha hb hc) (hdegree : i = j + m)
    (hyH : y ∈ D.homologyGrading m) :
    M.homologyRelation (by
      rw [hdegree] at hx
      exact add_mem hx (SetLike.mul_mem_graded ha hyH)) ha hb hc := by
  rcases hrelH with ⟨x', hx', hrel⟩
  let a' := homologyRepresentative D (a j)
  let b' := homologyRepresentative D (b k)
  let c' := homologyRepresentative D (c l)
  have ha' : DirectSum.of D.HomologyAt j (D.homogeneousClassOf a') = a := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D ha
  obtain ⟨y', hy'⟩ := M.representative_of_mem hyH
  subst x
  subst y
  subst i
  rw [M.relation_iff] at hrel
  rcases hrel with ⟨_, _, _, p, q, u, z, hp, hq, hpl, hjq, hdu, hdz, hout⟩
  have hqm : q = m := add_left_cancel (hjq.symm.trans rfl)
  subst q
  have hszy : masseySign j k l * (y'.1 : A) ∈ 𝒜 m := by
    have hmem := SetLike.mul_mem_graded (M.massey_sign_grading j k l) y'.1.2
    simpa using hmem
  let z' : 𝒜 m := ⟨(z : A) + masseySign j k l * (y'.1 : A), add_mem z.2 hszy⟩
  have hdz' : D.d (z' : A) = (b'.1 : A) * c'.1 := by
    change D.d (z' : A) =
      ((homologyRepresentative D (b k)).1 : A) * (homologyRepresentative D (c l)).1
    dsimp [z']
    rw [D.d.map_add, hdz]
    rcases M.massey_sign j k l with hs | hs
    · rw [hs, one_mul, D.homogeneousCycle_d y']
      simp
    · rw [hs, neg_one_mul, D.d.map_neg, D.homogeneousCycle_d y']
      simp
  let xnew : D.HomogeneousCycles (j + m) :=
    x' + D.homogeneousCycleMul a' y'
  have hnew : M.relation xnew.1 a'.1 b'.1 c'.1 := by
    rw [M.relation_iff]
    refine ⟨D.homogeneousCycle_d a', D.homogeneousCycle_d b',
      D.homogeneousCycle_d c', p, m, u, z', hp, hq, hpl, rfl, hdu, hdz', ?_⟩
    dsimp [xnew, z']
    rw [hout]
    rcases M.massey_sign j k l with hs | hs <;> rw [hs] <;>
      simp only [one_mul, neg_one_mul] <;> noncomm_ring
  refine ⟨xnew, ?_, hnew⟩
  dsimp [xnew]
  rw [← ha']
  rw [DirectSum.of_mul_of]
  change DirectSum.of D.HomologyAt (j + m)
      (D.homogeneousClassOf (x' + D.homogeneousCycleMul a' y')) =
    DirectSum.of D.HomologyAt (j + m) (D.homogeneousClassOf x') +
      DirectSum.of D.HomologyAt (j + m)
        (D.homologyMul (D.homogeneousClassOf a') (D.homogeneousClassOf y'))
  rw [D.homologyMul_classOf, ← map_add]
  rfl

theorem homology_indeterminacy_right
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {i j k l m : ι} {x a b c y : D.GradedHomology}
    {hx : x ∈ D.homologyGrading i} {ha : a ∈ D.homologyGrading j}
    {hb : b ∈ D.homologyGrading k} {hc : c ∈ D.homologyGrading l}
    (hrelH : M.homologyRelation hx ha hb hc) (hdegree : i = m + l)
    (hyH : y ∈ D.homologyGrading m) :
    M.homologyRelation (by
      rw [hdegree] at hx
      exact add_mem hx (SetLike.mul_mem_graded hyH hc)) ha hb hc := by
  rcases hrelH with ⟨x', hx', hrel⟩
  let a' := homologyRepresentative D (a j)
  let b' := homologyRepresentative D (b k)
  let c' := homologyRepresentative D (c l)
  have hc' : DirectSum.of D.HomologyAt l (D.homogeneousClassOf c') = c := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D hc
  obtain ⟨y', hy'⟩ := M.representative_of_mem hyH
  subst x
  subst y
  subst i
  rw [M.relation_iff] at hrel
  rcases hrel with ⟨_, _, _, p, q, u, z, hp, hq, hpl, hjq, hdu, hdz, hout⟩
  have hpm : p = m := add_right_cancel (hpl.symm.trans rfl)
  subst p
  let u' : 𝒜 m := u + y'.1
  have hdu' : D.d (u' : A) = (a'.1 : A) * b'.1 := by
    change D.d (u' : A) =
      ((homologyRepresentative D (a j)).1 : A) * (homologyRepresentative D (b k)).1
    dsimp [u']
    rw [D.d.map_add, hdu, D.homogeneousCycle_d y', add_zero]
  let xnew : D.HomogeneousCycles (m + l) :=
    x' + D.homogeneousCycleMul y' c'
  have hnew : M.relation xnew.1 a'.1 b'.1 c'.1 := by
    rw [M.relation_iff]
    refine ⟨D.homogeneousCycle_d a', D.homogeneousCycle_d b',
      D.homogeneousCycle_d c', m, q, u', z, hp, hq, rfl, hjq, hdu', hdz, ?_⟩
    dsimp [xnew, u']
    rw [hout]
    noncomm_ring
  refine ⟨xnew, ?_, hnew⟩
  dsimp [xnew]
  rw [← hc']
  rw [DirectSum.of_mul_of]
  change DirectSum.of D.HomologyAt (m + l)
      (D.homogeneousClassOf (x' + D.homogeneousCycleMul y' c')) =
    DirectSum.of D.HomologyAt (m + l) (D.homogeneousClassOf x') +
      DirectSum.of D.HomologyAt (m + l)
        (D.homologyMul (D.homogeneousClassOf y') (D.homogeneousClassOf c'))
  rw [D.homologyMul_classOf, ← map_add]
  rfl

theorem homology_indeterminacy_complete
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {i j k l : ι} {x₁ x₂ a b c : D.GradedHomology}
    {hx₁ : x₁ ∈ D.homologyGrading i} {hx₂ : x₂ ∈ D.homologyGrading i}
    {ha : a ∈ D.homologyGrading j} {hb : b ∈ D.homologyGrading k}
    {hc : c ∈ D.homologyGrading l}
    (h₁ : M.homologyRelation hx₁ ha hb hc) (h₂ : M.homologyRelation hx₂ ha hb hc) :
    ∃ (m n : ι) (y z : D.GradedHomology), y ∈ D.homologyGrading m ∧
      z ∈ D.homologyGrading n ∧ i = j + m ∧ i = n + l ∧
      x₁ - x₂ = a * y + z * c := by
  rcases h₁ with ⟨x₁', hx₁', hrel₁⟩
  rcases h₂ with ⟨x₂', hx₂', hrel₂⟩
  let a' := homologyRepresentative D (a j)
  let b' := homologyRepresentative D (b k)
  let c' := homologyRepresentative D (c l)
  have ha' : DirectSum.of D.HomologyAt j (D.homogeneousClassOf a') = a := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D ha
  have hc' : DirectSum.of D.HomologyAt l (D.homogeneousClassOf c') = c := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D hc
  rw [M.relation_iff] at hrel₁ hrel₂
  rcases hrel₁ with ⟨_, _, _, p₁, q₁, u₁, z₁, hp₁, hq₁, hpl₁, hjq₁, hdu₁, hdz₁, hout₁⟩
  rcases hrel₂ with ⟨_, _, _, p₂, q₂, u₂, z₂, hp₂, hq₂, hpl₂, hjq₂, hdu₂, hdz₂, hout₂⟩
  subst i
  have hp : p₁ = p₂ := add_right_cancel hpl₂
  have hq : q₁ = q₂ := add_left_cancel (hjq₁.symm.trans hjq₂)
  subst p₂
  subst q₂
  have hsMem : masseySign j k l * ((z₁ : A) - z₂) ∈ 𝒜 q₁ := by
    have hmem := SetLike.mul_mem_graded (M.massey_sign_grading j k l) (sub_mem z₁.2 z₂.2)
    simpa using hmem
  let y' : D.HomogeneousCycles q₁ :=
    ⟨⟨masseySign j k l * ((z₁ : A) - z₂), hsMem⟩, by
      change D.d (masseySign j k l * ((z₁ : A) - z₂)) = 0
      rcases M.massey_sign j k l with hs | hs
      · rw [hs, one_mul, D.d.map_sub, hdz₁, hdz₂, sub_self]
      · rw [hs, neg_one_mul, D.d.map_neg, D.d.map_sub, hdz₁, hdz₂,
          sub_self, neg_zero]⟩
  let z' : D.HomogeneousCycles p₁ :=
    ⟨u₁ - u₂, by
      change D.d ((u₁ : A) - u₂) = 0
      rw [D.d.map_sub, hdu₁, hdu₂, sub_self]⟩
  let y := DirectSum.of D.HomologyAt q₁ (D.homogeneousClassOf y')
  let z := DirectSum.of D.HomologyAt p₁ (D.homogeneousClassOf z')
  refine ⟨q₁, p₁, y, z, ⟨_, rfl⟩, ⟨_, rfl⟩, hjq₁, rfl, ?_⟩
  rw [← hx₁', ← hx₂', ← ha', ← hc']
  dsimp [y, z]
  rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
  rw [show GradedMonoid.GMul.mul (D.homogeneousClassOf a') (D.homogeneousClassOf y') =
        D.homogeneousClassOf (D.homogeneousCycleMul a' y') from rfl,
    show GradedMonoid.GMul.mul (D.homogeneousClassOf z') (D.homogeneousClassOf c') =
        D.homogeneousClassOf (D.homogeneousCycleMul z' c') from rfl]
  rw [directSum_of_cast hjq₁.symm
    (D.homogeneousClassOf (D.homogeneousCycleMul a' y'))]
  rw [← map_sub, ← map_add]
  apply congrArg (DirectSum.of D.HomologyAt (p₁ + l))
  rw [D.cast_homogeneousClassOf]
  change D.homogeneousClassOf (x₁' - x₂') =
    D.homogeneousClassOf
      (cast (congrArg D.HomogeneousCycles hjq₁.symm)
        (D.homogeneousCycleMul a' y') + D.homogeneousCycleMul z' c')
  apply congrArg D.homogeneousClassOf
  apply Subtype.ext
  apply Subtype.ext
  dsimp [y', z']
  rw [D.coe_cast_homogeneousCycle, hout₁, hout₂]
  change
    (u₁ : A) * c'.1 + masseySign j k l * ((a'.1 : A) * z₁) -
        ((u₂ : A) * c'.1 + masseySign j k l * ((a'.1 : A) * z₂)) =
      (a'.1 : A) * (masseySign j k l * ((z₁ : A) - z₂)) +
        ((u₁ : A) - u₂) * c'.1
  rcases M.massey_sign j k l with hs | hs <;> rw [hs] <;>
    simp only [one_mul, neg_one_mul] <;> noncomm_ring
  all_goals exact hjq₁.symm

theorem homology_juggling
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign)
    {i j k l m : ι} {x a b c d : D.GradedHomology}
    {hx : x ∈ D.homologyGrading i} {ha : a ∈ D.homologyGrading j}
    {hb : b ∈ D.homologyGrading k} {hc : c ∈ D.homologyGrading l}
    {hd : d ∈ D.homologyGrading m}
    (hrelH : M.homologyRelation hx ha hb hc) (hcd : c * d = 0) :
    ∃ y : D.GradedHomology, ∃ hy : y ∈ D.homologyGrading (masseyGrading k l m),
      M.homologyRelation hy hb hc hd ∧
        x * d = M.homologyJugglingSign i j k l * (a * y) := by
  rcases hrelH with ⟨x', hx', hrel⟩
  let a' := homologyRepresentative D (a j)
  let b' := homologyRepresentative D (b k)
  let c' := homologyRepresentative D (c l)
  let d' := homologyRepresentative D (d m)
  have ha' : DirectSum.of D.HomologyAt j (D.homogeneousClassOf a') = a := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D ha
  have hc' : DirectSum.of D.HomologyAt l (D.homogeneousClassOf c') = c := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D hc
  have hd' : DirectSum.of D.HomologyAt m (D.homogeneousClassOf d') = d := by
    rw [class_homologyRepresentative]
    exact of_component_eq_of_mem D hd
  rw [M.relation_iff] at hrel
  rcases hrel with ⟨_, _, _, p, q, u, z, hp, hq, hpl, hjq, hdu, hdz, hout⟩
  subst i
  rw [← hc', ← hd'] at hcd
  obtain ⟨r, w, hr, hdw⟩ := M.boundary_data (M.product_boundary_of_zero c' d' hcd)
  have hqm : q + m = k + r := by
    apply D.dDegree_injective
    rw [D.dDegree_left, D.dDegree_right, hq, hr, add_assoc]
  have hsMem : masseySign k l m * ((b'.1 : A) * w) ∈ 𝒜 (q + m) := by
    have hmem := SetLike.mul_mem_graded (M.massey_sign_grading k l m)
      (SetLike.mul_mem_graded b'.1.2 w.2)
    simpa [hqm] using hmem
  have hvMem : (z : A) * d'.1 + masseySign k l m * ((b'.1 : A) * w) ∈
      𝒜 (q + m) :=
    add_mem (SetLike.mul_mem_graded z.2 d'.1.2) hsMem
  let v0 : 𝒜 (q + m) :=
    ⟨(z : A) * d'.1 + masseySign k l m * ((b'.1 : A) * w), hvMem⟩
  have hvCycle : D.d (v0 : A) = 0 := by
    dsimp [v0]
    rw [D.d.map_add, D.leibniz z.2, hdz, D.homogeneousCycle_d d']
    simp only [mul_zero, add_zero]
    rcases M.massey_sign k l m with hs | hs
    · rw [hs, one_mul, D.leibniz b'.1.2, D.homogeneousCycle_d b', hdw,
        zero_mul, zero_add]
      have hcycle := M.cycle_sign k l m
      rw [hs, one_mul] at hcycle
      rw [hcycle]
      noncomm_ring
    · rw [hs, neg_one_mul, D.d.map_neg, D.leibniz b'.1.2,
        D.homogeneousCycle_d b', hdw, zero_mul, zero_add]
      have hcycle := M.cycle_sign k l m
      rw [hs, neg_one_mul] at hcycle
      have heps : leibnizSign k = 1 := by simpa using hcycle
      rw [heps]
      noncomm_ring
  let v' : D.HomogeneousCycles (q + m) := ⟨v0, hvCycle⟩
  have hnext : M.relation v'.1 b'.1 c'.1 d'.1 := by
    rw [M.relation_iff]
    exact ⟨D.homogeneousCycle_d b', D.homogeneousCycle_d c',
      D.homogeneousCycle_d d', q, r, z, w, hq, hr, rfl, hqm, hdz, hdw, rfl⟩
  have hgrade : q + m = masseyGrading k l m := M.relation_grading hnext
  let v'' : D.HomogeneousCycles (masseyGrading k l m) :=
    cast (congrArg D.HomogeneousCycles hgrade) v'
  let y := DirectSum.of D.HomologyAt (masseyGrading k l m)
    (D.homogeneousClassOf v'')
  have hy : y ∈ D.homologyGrading (masseyGrading k l m) := ⟨_, rfl⟩
  refine ⟨y, hy, ?_, ?_⟩
  · refine ⟨v'', rfl, ?_⟩
    rw [M.relation_iff]
    refine ⟨D.homogeneousCycle_d b', D.homogeneousCycle_d c',
      D.homogeneousCycle_d d', q, r, z, w, hq, hr, hgrade.symm,
      hgrade.symm.trans hqm, hdz, hdw, ?_⟩
    rw [D.coe_cast_homogeneousCycle]
    all_goals first | rfl | exact hgrade
  · have hdeg : (p + l) + m = j + (q + m) := by
      calc
        (p + l) + m = (j + q) + m := congrArg (fun t => t + m) hjq
        _ = j + (q + m) := add_assoc j q m
    have hpre : dDegree (p + r) = (p + l) + m := by
      rw [D.dDegree_right, hr, add_assoc]
    have hwMem : leibnizSign p * ((u : A) * w) ∈ 𝒜 (p + r) := by
      have hmem := SetLike.mul_mem_graded (D.leibniz_sign_grading p)
        (SetLike.mul_mem_graded u.2 w.2)
      simpa using hmem
    have hboundary : D.HomogeneousBoundary ((p + l) + m)
        (((x'.1 : A) * d'.1) -
          masseySign j k l * ((a'.1 : A) * v'.1)) := by
      refine Or.inr ⟨p + r, ⟨leibnizSign p * ((u : A) * w), hwMem⟩, hpre, ?_⟩
      have hdWitness :
          D.d (leibnizSign p * ((u : A) * w)) =
            leibnizSign p * (D.d (u : A) * w) + (u : A) * D.d (w : A) := by
        rcases D.leibniz_sign p with heps | heps
        · rw [heps, one_mul, D.leibniz u.2, heps]
          noncomm_ring
        · rw [heps, neg_one_mul, D.d.map_neg, D.leibniz u.2, heps]
          noncomm_ring
      rw [hout]
      dsimp [v', v0]
      calc
        ((u : A) * c'.1 + masseySign j k l * ((a'.1 : A) * z)) * d'.1 -
              masseySign j k l * ((a'.1 : A) *
                ((z : A) * d'.1 + masseySign k l m * ((b'.1 : A) * w))) =
            (u : A) * (c'.1 * d'.1) -
              (masseySign j k l * masseySign k l m) *
                (((a'.1 : A) * b'.1) * w) := by
                  rcases M.massey_sign j k l with hs₁ | hs₁ <;>
                    rcases M.massey_sign k l m with hs₂ | hs₂ <;>
                    rw [hs₁, hs₂] <;> simp only [one_mul, neg_one_mul] <;>
                    noncomm_ring
        _ = leibnizSign p * (D.d (u : A) * w) +
              (u : A) * D.d (w : A) := by
                rw [hdw, hdu, M.juggling_sign_coherence j k l m p hp]
                noncomm_ring
        _ = D.d (leibnizSign p * ((u : A) * w)) := hdWitness.symm
    have hyRaw : DirectSum.of D.HomologyAt (q + m) (D.homogeneousClassOf v') = y := by
      dsimp [y, v'']
      rw [← D.cast_homogeneousClassOf]
      exact directSum_of_cast hgrade (D.homogeneousClassOf v')
      all_goals exact hgrade
    rw [← hx', ← hd', ← ha', ← hyRaw]
    unfold homologyJugglingSign
    rcases M.massey_sign j k l with hs | hs
    · have hsCycle : M.homologySignCycle j k l = D.homogeneousOne := by
        apply Subtype.ext
        apply Subtype.ext
        exact hs
      rw [hsCycle]
      rw [show DirectSum.of D.HomologyAt 0
          (D.homogeneousClassOf D.homogeneousOne) = (1 : D.GradedHomology) from rfl,
        one_mul, DirectSum.of_mul_of, DirectSum.of_mul_of]
      have hclass : D.homogeneousClassOf (D.homogeneousCycleMul x' d') =
          D.homogeneousClassOf
            (cast (congrArg D.HomogeneousCycles hdeg.symm)
              (D.homogeneousCycleMul a' v')) := by
        apply Quotient.sound
        change D.HomogeneousBoundary ((p + l) + m)
          (((x'.1 : A) * d'.1) -
            ((cast (congrArg D.HomogeneousCycles hdeg.symm)
              (D.homogeneousCycleMul a' v')).1 : A))
        rw [D.coe_cast_homogeneousCycle]
        show D.HomogeneousBoundary ((p + l) + m)
          ((x'.1 : A) * d'.1 - (a'.1 : A) * v'.1)
        simpa [hs] using hboundary
        exact hdeg.symm
      change
        DirectSum.of D.HomologyAt ((p + l) + m)
            (D.homogeneousClassOf (D.homogeneousCycleMul x' d')) =
          DirectSum.of D.HomologyAt (j + (q + m))
            (D.homogeneousClassOf (D.homogeneousCycleMul a' v'))
      rw [directSum_of_cast hdeg.symm
        (D.homogeneousClassOf (D.homogeneousCycleMul a' v'))]
      apply congrArg (DirectSum.of D.HomologyAt ((p + l) + m))
      rw [D.cast_homogeneousClassOf]
      exact hclass
      all_goals exact hdeg.symm
    · have hsCycle : M.homologySignCycle j k l = -D.homogeneousOne := by
        apply Subtype.ext
        apply Subtype.ext
        change (masseySign j k l : A) = -1
        exact hs
      rw [hsCycle]
      have hsignTotal : DirectSum.of D.HomologyAt 0
          (D.homogeneousClassOf (-D.homogeneousOne)) = -(1 : D.GradedHomology) := by
        change DirectSum.of D.HomologyAt 0
          (-D.homogeneousClassOf D.homogeneousOne) = -(1 : D.GradedHomology)
        rw [map_neg]
        rfl
      rw [hsignTotal, neg_mul, DirectSum.of_mul_of, DirectSum.of_mul_of, one_mul]
      have hclass : D.homogeneousClassOf (D.homogeneousCycleMul x' d') =
          D.homogeneousClassOf
            (cast (congrArg D.HomogeneousCycles hdeg.symm)
              (-(D.homogeneousCycleMul a' v'))) := by
        apply Quotient.sound
        change D.HomogeneousBoundary ((p + l) + m)
          (((x'.1 : A) * d'.1) -
            ((cast (congrArg D.HomogeneousCycles hdeg.symm)
              (-(D.homogeneousCycleMul a' v'))).1 : A))
        rw [D.coe_cast_homogeneousCycle]
        show D.HomogeneousBoundary ((p + l) + m)
          ((x'.1 : A) * d'.1 - (-((D.homogeneousCycleMul (i := j)
            a' v' : D.HomogeneousCycles (j + (q + m))) : A)))
        simpa [hs, DGA.homogeneousCycleMul] using hboundary
        exact hdeg.symm
      change
        DirectSum.of D.HomologyAt ((p + l) + m)
            (D.homogeneousClassOf (D.homogeneousCycleMul x' d')) =
          -(DirectSum.of D.HomologyAt (j + (q + m))
            (D.homogeneousClassOf (D.homogeneousCycleMul a' v')))
      rw [directSum_of_cast hdeg.symm
        (D.homogeneousClassOf (D.homogeneousCycleMul a' v')), ← map_neg]
      apply congrArg (DirectSum.of D.HomologyAt ((p + l) + m))
      rw [D.cast_homogeneousClassOf]
      rw [cast_neg_homogeneousCycle] at hclass
      change D.homogeneousClassOf (D.homogeneousCycleMul x' d') =
        -D.homogeneousClassOf
          (cast (congrArg D.HomogeneousCycles hdeg.symm)
            (D.homogeneousCycleMul a' v')) at hclass
      exact hclass
      all_goals exact hdeg.symm

noncomputable instance homologyTodaBracket
    (M : MasseyProduct A 𝒜 dDegree leibnizSign D masseyGrading masseySign) :
    TodaBracket D.homologyGrading masseyGrading M.homologyJugglingSign where
  juggling_grading := M.juggling_grading
  juggling_sign := M.homologyJugglingSign_eq_one_or_neg_one
  relation := M.homologyRelation
  composable := M.homology_composable
  grading_axiom := M.homology_grading
  indeterminacy_left := M.homology_indeterminacy_left
  indeterminacy_right := M.homology_indeterminacy_right
  indeterminacy_complete := M.homology_indeterminacy_complete
  juggling := M.homology_juggling
  exists_relation := M.homology_exists_relation

end MasseyProduct

end KIPBase.SpectralSequence
