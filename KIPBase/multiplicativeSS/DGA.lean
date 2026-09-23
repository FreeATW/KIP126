import KIPBase.Mathlib

namespace KIPBase.SpectralSequence

open scoped DirectSum

universe u v w

class DGA (A : Type u) [Ring A] {ι : Type v} [AddMonoid ι] [DecidableEq ι]
    {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    (dDegree : ι → ι) (leibnizSign : ι → A) where
  d : A →+ A
  d_square : ∀ a : A, d (d a) = 0
  d_one : d 1 = 0
  dDegree_injective : Function.Injective dDegree
  dDegree_left : ∀ i j : ι, dDegree (i + j) = dDegree i + j
  dDegree_right : ∀ i j : ι, dDegree (i + j) = i + dDegree j
  d_grading : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → d a ∈ 𝒜 (dDegree i)
  leibniz_sign : ∀ i : ι, leibnizSign i = 1 ∨ leibnizSign i = -1
  leibniz_sign_grading : ∀ i : ι, leibnizSign i ∈ 𝒜 0
  leibniz : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A,
    d (a * b) = d a * b + leibnizSign i * (a * d b)

namespace DGA

variable {A : Type u} [Ring A] {ι : Type v} [AddMonoid ι] [DecidableEq ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ι → σ} [GradedRing 𝒜] {dDegree : ι → ι} {leibnizSign : ι → A}

def Cycles (D : DGA A 𝒜 dDegree leibnizSign) := {a : A // D.d a = 0}

def homogeneousCyclesAddSubgroup (D : DGA A 𝒜 dDegree leibnizSign) (i : ι) :
    AddSubgroup (𝒜 i) :=
  (D.d.comp (AddSubgroupClass.subtype (𝒜 i))).ker

abbrev HomogeneousCycles (D : DGA A 𝒜 dDegree leibnizSign) (i : ι) : Type u :=
  D.homogeneousCyclesAddSubgroup i

@[simp]
theorem homogeneousCycle_d (D : DGA A 𝒜 dDegree leibnizSign) {i : ι}
    (a : D.HomogeneousCycles i) : D.d (a.1 : A) = 0 :=
  a.2

def HomogeneousBoundary (D : DGA A 𝒜 dDegree leibnizSign) (i : ι) (a : A) : Prop :=
  a = 0 ∨ ∃ (p : ι) (y : 𝒜 p), dDegree p = i ∧ a = D.d (y : A)

theorem homogeneousBoundary_add (D : DGA A 𝒜 dDegree leibnizSign) {i : ι}
    {x y : A} (hx : D.HomogeneousBoundary i x) (hy : D.HomogeneousBoundary i y) :
    D.HomogeneousBoundary i (x + y) := by
  rcases hx with hx | ⟨p, u, hp, hu⟩
  · rw [hx, zero_add]
    exact hy
  · rcases hy with hy | ⟨q, v, hq, hv⟩
    · rw [hy, add_zero]
      exact Or.inr ⟨p, u, hp, hu⟩
    · have hpq : p = q := D.dDegree_injective (hp.trans hq.symm)
      subst q
      refine Or.inr ⟨p, u + v, hp, ?_⟩
      calc
        x + y = D.d (u : A) + D.d (v : A) := by rw [hu, hv]
        _ = D.d ((u : A) + v) := (D.d.map_add (u : A) v).symm

def homologySetoid (D : DGA A 𝒜 dDegree leibnizSign) : Setoid D.Cycles where
  r a b := ∃ y : A, a.1 - b.1 = D.d y
  iseqv := by
    constructor
    · intro a
      exact ⟨0, by simp⟩
    · intro a b hab
      rcases hab with ⟨y, hy⟩
      refine ⟨-y, ?_⟩
      calc
        b.1 - a.1 = -(a.1 - b.1) := by simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
        _ = -(D.d y) := by rw [hy]
        _ = D.d (-y) := (D.d.map_neg y).symm
    · intro a b c hab hbc
      rcases hab with ⟨y, hy⟩
      rcases hbc with ⟨z, hz⟩
      refine ⟨y + z, ?_⟩
      calc
        a.1 - c.1 = (a.1 - b.1) + (b.1 - c.1) := by
          simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]
        _ = D.d y + D.d z := by rw [hy, hz]
        _ = D.d (y + z) := (D.d.map_add y z).symm

def Homology (D : DGA A 𝒜 dDegree leibnizSign) := Quotient D.homologySetoid

def classOf (D : DGA A 𝒜 dDegree leibnizSign) (a : D.Cycles) : D.Homology :=
  Quotient.mk _ a

def homogeneousCycleToCycle (D : DGA A 𝒜 dDegree leibnizSign) {i : ι}
    (a : D.HomogeneousCycles i) : D.Cycles :=
  ⟨a.1.1, a.2⟩

def homogeneousHomologyAddCon (D : DGA A 𝒜 dDegree leibnizSign) (i : ι) :
    AddCon (D.HomogeneousCycles i) where
  r a b := D.HomogeneousBoundary i ((a.1 : A) - b.1)
  iseqv := by
    constructor
    · intro a
      exact Or.inl (sub_self (a.1 : A))
    · intro a b hab
      rcases hab with hab | ⟨p, y, hp, hy⟩
      · exact Or.inl (sub_eq_zero.mpr (sub_eq_zero.mp hab).symm)
      · refine Or.inr ⟨p, -y, hp, ?_⟩
        calc
          (b.1 : A) - a.1 = -((a.1 : A) - b.1) := by noncomm_ring
          _ = -(D.d (y : A)) := by rw [hy]
          _ = D.d (-(y : A)) := (D.d.map_neg (y : A)).symm
    · intro a b c hab hbc
      rcases hab with hab | ⟨p, y, hp, hy⟩
      · have hab' : (a.1 : A) = b.1 := sub_eq_zero.mp hab
        rw [hab']
        exact hbc
      · rcases hbc with hbc | ⟨q, z, hq, hz⟩
        · have hbc' : (b.1 : A) = c.1 := sub_eq_zero.mp hbc
          rw [hbc'] at hy
          exact Or.inr ⟨p, y, hp, hy⟩
        · have hpq : p = q := D.dDegree_injective (hp.trans hq.symm)
          subst q
          refine Or.inr ⟨p, y + z, hp, ?_⟩
          calc
            (a.1 : A) - c.1 = ((a.1 : A) - b.1) + ((b.1 : A) - c.1) := by
              noncomm_ring
            _ = D.d (y : A) + D.d (z : A) := by rw [hy, hz]
            _ = D.d ((y : A) + z) := (D.d.map_add (y : A) z).symm
  add' := by
    intro a a' b b' ha hb
    have h := D.homogeneousBoundary_add ha hb
    change D.HomogeneousBoundary i
      (((a.1 : A) + b.1) - ((a'.1 : A) + b'.1))
    convert h using 1
    noncomm_ring

def HomologyAt (D : DGA A 𝒜 dDegree leibnizSign) (i : ι) :=
  (D.homogeneousHomologyAddCon i).Quotient

instance homologyAtAddCommGroup (D : DGA A 𝒜 dDegree leibnizSign) (i : ι) :
    AddCommGroup (D.HomologyAt i) :=
  AddCon.addCommGroup (D.homogeneousHomologyAddCon i)

def homogeneousClassOf (D : DGA A 𝒜 dDegree leibnizSign) {i : ι}
    (a : D.HomogeneousCycles i) : D.HomologyAt i :=
  AddCon.toQuotient a

theorem cast_homogeneousClassOf (D : DGA A 𝒜 dDegree leibnizSign)
    {i j : ι} (h : i = j) (a : D.HomogeneousCycles i) :
    cast (congrArg D.HomologyAt h) (D.homogeneousClassOf a) =
      D.homogeneousClassOf (cast (congrArg D.HomogeneousCycles h) a) := by
  subst j
  rfl

@[simp]
theorem coe_cast_homogeneousCycle (D : DGA A 𝒜 dDegree leibnizSign)
    {i j : ι} (h : i = j) (a : D.HomogeneousCycles i) :
    ((cast (congrArg D.HomogeneousCycles h) a).1 : A) = (a.1 : A) := by
  subst j
  rfl

def homogeneousCycleMul (D : DGA A 𝒜 dDegree leibnizSign) {i j : ι}
    (a : D.HomogeneousCycles i) (b : D.HomogeneousCycles j) :
    D.HomogeneousCycles (i + j) :=
  ⟨⟨(a.1 : A) * b.1, SetLike.mul_mem_graded a.1.2 b.1.2⟩, by
    change D.d ((a.1 : A) * b.1) = 0
    rw [D.leibniz a.1.2, D.homogeneousCycle_d a, D.homogeneousCycle_d b]
    simp⟩

theorem d_mul_homogeneousCycle (D : DGA A 𝒜 dDegree leibnizSign) {p j : ι}
    (y : 𝒜 p) (b : D.HomogeneousCycles j) :
    D.d ((y : A) * b.1) = D.d (y : A) * b.1 := by
  rw [D.leibniz y.2, D.homogeneousCycle_d b]
  simp

theorem homogeneousCycle_mul_d_isBoundary (D : DGA A 𝒜 dDegree leibnizSign) {i q : ι}
    (a : D.HomogeneousCycles i) (z : 𝒜 q) :
    ∃ w : A, D.d w = (a.1 : A) * D.d (z : A) := by
  rcases D.leibniz_sign i with hsign | hsign
  · refine ⟨(a.1 : A) * z, ?_⟩
    rw [D.leibniz a.1.2, D.homogeneousCycle_d a, hsign]
    simp
  · refine ⟨-((a.1 : A) * z), ?_⟩
    rw [D.d.map_neg, D.leibniz a.1.2, D.homogeneousCycle_d a, hsign]
    simp

theorem homogeneousBoundary_mul_right (D : DGA A 𝒜 dDegree leibnizSign)
    {i j : ι} {a a' : D.HomogeneousCycles i} (b : D.HomogeneousCycles j)
    (ha : D.HomogeneousBoundary i ((a.1 : A) - a'.1)) :
    D.HomogeneousBoundary (i + j)
      ((D.homogeneousCycleMul a b).1 - (D.homogeneousCycleMul a' b).1) := by
  rcases ha with ha | ⟨p, u, hp, hu⟩
  · have haa' : (a.1 : A) = a'.1 := sub_eq_zero.mp ha
    exact Or.inl (by simp [homogeneousCycleMul, haa'])
  · refine Or.inr ⟨p + j,
      ⟨(u : A) * b.1, SetLike.mul_mem_graded u.2 b.1.2⟩, ?_, ?_⟩
    · rw [D.dDegree_left, hp]
    · calc
        (D.homogeneousCycleMul a b).1 - (D.homogeneousCycleMul a' b).1 =
            ((a.1 : A) - a'.1) * b.1 := by simp [homogeneousCycleMul]; noncomm_ring
        _ = D.d (u : A) * b.1 := by rw [hu]
        _ = D.d ((u : A) * b.1) := (D.d_mul_homogeneousCycle u b).symm

theorem homogeneousBoundary_mul_left (D : DGA A 𝒜 dDegree leibnizSign)
    {i j : ι} (a : D.HomogeneousCycles i) {b b' : D.HomogeneousCycles j}
    (hb : D.HomogeneousBoundary j ((b.1 : A) - b'.1)) :
    D.HomogeneousBoundary (i + j)
      ((D.homogeneousCycleMul a b).1 - (D.homogeneousCycleMul a b').1) := by
  rcases hb with hb | ⟨q, v, hq, hv⟩
  · have hbb' : (b.1 : A) = b'.1 := sub_eq_zero.mp hb
    exact Or.inl (by simp [homogeneousCycleMul, hbb'])
  · rcases D.leibniz_sign i with hsign | hsign
    · refine Or.inr ⟨i + q,
        ⟨(a.1 : A) * v, SetLike.mul_mem_graded a.1.2 v.2⟩, ?_, ?_⟩
      · rw [D.dDegree_right, hq]
      · calc
          (D.homogeneousCycleMul a b).1 - (D.homogeneousCycleMul a b').1 =
              (a.1 : A) * ((b.1 : A) - b'.1) := by simp [homogeneousCycleMul]; noncomm_ring
          _ = (a.1 : A) * D.d (v : A) := by rw [hv]
          _ = D.d ((a.1 : A) * v) := by
            rw [D.leibniz a.1.2, D.homogeneousCycle_d a, hsign]
            simp
    · refine Or.inr ⟨i + q,
        ⟨-((a.1 : A) * v), neg_mem (SetLike.mul_mem_graded a.1.2 v.2)⟩, ?_, ?_⟩
      · rw [D.dDegree_right, hq]
      · calc
          (D.homogeneousCycleMul a b).1 - (D.homogeneousCycleMul a b').1 =
              (a.1 : A) * ((b.1 : A) - b'.1) := by simp [homogeneousCycleMul]; noncomm_ring
          _ = (a.1 : A) * D.d (v : A) := by rw [hv]
          _ = D.d (-((a.1 : A) * v)) := by
            rw [D.d.map_neg, D.leibniz a.1.2, D.homogeneousCycle_d a, hsign]
            simp

theorem homogeneousCycleMul_respects (D : DGA A 𝒜 dDegree leibnizSign)
    {i j : ι} {a a' : D.HomogeneousCycles i} {b b' : D.HomogeneousCycles j}
    (ha : D.homogeneousHomologyAddCon i a a')
    (hb : D.homogeneousHomologyAddCon j b b') :
    D.homogeneousHomologyAddCon (i + j)
      (D.homogeneousCycleMul a b) (D.homogeneousCycleMul a' b') := by
  change D.HomogeneousBoundary (i + j)
    ((D.homogeneousCycleMul a b).1 - (D.homogeneousCycleMul a' b').1)
  have hright := D.homogeneousBoundary_mul_right b ha
  have hleft := D.homogeneousBoundary_mul_left a' hb
  have hsum := D.homogeneousBoundary_add hright hleft
  convert hsum using 1
  noncomm_ring

def homologyMul (D : DGA A 𝒜 dDegree leibnizSign) {i j : ι} :
    D.HomologyAt i → D.HomologyAt j → D.HomologyAt (i + j) :=
  Quotient.map₂ D.homogeneousCycleMul (fun _ _ ha _ _ hb =>
    D.homogeneousCycleMul_respects ha hb)

@[simp]
theorem homologyMul_classOf (D : DGA A 𝒜 dDegree leibnizSign) {i j : ι}
    (a : D.HomogeneousCycles i) (b : D.HomogeneousCycles j) :
    D.homologyMul (D.homogeneousClassOf a) (D.homogeneousClassOf b) =
      D.homogeneousClassOf (D.homogeneousCycleMul a b) :=
  rfl

/-- The multiplication induced on homogeneous homology is associative.

This is the elementwise homological descent behind the usual assertion that
the product on the next page of a multiplicative spectral sequence is
associative.  The left side is transported along `(i + j) + k = i + (j + k)`;
the proof reduces to the associativity of multiplication in `A` on cycle
representatives, and therefore does not assume associativity as an extra
property of homology multiplication. -/
theorem homologyMul_assoc (D : DGA A 𝒜 dDegree leibnizSign) {i j k : ι}
    (x : D.HomologyAt i) (y : D.HomologyAt j) (z : D.HomologyAt k) :
    cast (congrArg D.HomologyAt (add_assoc i j k))
        (D.homologyMul (D.homologyMul x y) z) =
      D.homologyMul x (D.homologyMul y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  change cast (congrArg D.HomologyAt (add_assoc i j k))
      (D.homogeneousClassOf (D.homogeneousCycleMul (D.homogeneousCycleMul a b) c)) =
    D.homogeneousClassOf (D.homogeneousCycleMul a (D.homogeneousCycleMul b c))
  rw [D.cast_homogeneousClassOf]
  apply congrArg D.homogeneousClassOf
  apply Subtype.ext
  apply Subtype.ext
  all_goals try exact add_assoc i j k
  rw [D.coe_cast_homogeneousCycle]
  simp [homogeneousCycleMul, mul_assoc]
  all_goals exact add_assoc i j k

instance homologyGMul (D : DGA A 𝒜 dDegree leibnizSign) :
    GradedMonoid.GMul D.HomologyAt where
  mul := D.homologyMul

instance homologyGNonUnitalNonAssocSemiring
    (D : DGA A 𝒜 dDegree leibnizSign) :
    DirectSum.GNonUnitalNonAssocSemiring D.HomologyAt where
  mul_zero := by
    intro i j a
    refine Quotient.inductionOn a ?_
    intro a₀
    change D.homogeneousClassOf (D.homogeneousCycleMul a₀ 0) = D.homogeneousClassOf 0
    apply congrArg D.homogeneousClassOf
    ext
    simp [homogeneousCycleMul]
  zero_mul := by
    intro i j b
    refine Quotient.inductionOn b ?_
    intro b₀
    change D.homogeneousClassOf (D.homogeneousCycleMul 0 b₀) = D.homogeneousClassOf 0
    apply congrArg D.homogeneousClassOf
    ext
    simp [homogeneousCycleMul]
  mul_add := by
    intro i j a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro a₀ b₀ c₀
    change D.homogeneousClassOf (D.homogeneousCycleMul a₀ (b₀ + c₀)) =
      D.homogeneousClassOf (D.homogeneousCycleMul a₀ b₀ + D.homogeneousCycleMul a₀ c₀)
    apply congrArg D.homogeneousClassOf
    ext
    simp [homogeneousCycleMul, mul_add]
  add_mul := by
    intro i j a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro a₀ b₀ c₀
    change D.homogeneousClassOf (D.homogeneousCycleMul (a₀ + b₀) c₀) =
      D.homogeneousClassOf (D.homogeneousCycleMul a₀ c₀ + D.homogeneousCycleMul b₀ c₀)
    apply congrArg D.homogeneousClassOf
    ext
    simp [homogeneousCycleMul, add_mul]

def homogeneousOne (D : DGA A 𝒜 dDegree leibnizSign) : D.HomogeneousCycles 0 :=
  ⟨⟨1, SetLike.one_mem_graded 𝒜⟩, D.d_one⟩

instance homologyGOne (D : DGA A 𝒜 dDegree leibnizSign) :
    GradedMonoid.GOne D.HomologyAt where
  one := D.homogeneousClassOf D.homogeneousOne

instance homologyGMonoid (D : DGA A 𝒜 dDegree leibnizSign) :
    GradedMonoid.GMonoid D.HomologyAt where
  one_mul := by
    rintro ⟨i, x⟩
    refine Quotient.inductionOn x ?_
    intro a
    change GradedMonoid.mk (0 + i)
      (D.homologyMul (D.homogeneousClassOf D.homogeneousOne) (D.homogeneousClassOf a)) =
      GradedMonoid.mk i (D.homogeneousClassOf a)
    apply Sigma.ext (zero_add i)
    apply heq_of_cast_eq (congrArg D.HomologyAt (zero_add i))
    change cast (congrArg D.HomologyAt (zero_add i))
      (D.homogeneousClassOf (D.homogeneousCycleMul D.homogeneousOne a)) =
      D.homogeneousClassOf a
    rw [D.cast_homogeneousClassOf]
    apply congrArg D.homogeneousClassOf
    apply Subtype.ext
    apply Subtype.ext
    all_goals try exact zero_add i
    rw [D.coe_cast_homogeneousCycle]
    simp [homogeneousCycleMul, homogeneousOne]
    all_goals exact zero_add i
  mul_one := by
    rintro ⟨i, x⟩
    refine Quotient.inductionOn x ?_
    intro a
    change GradedMonoid.mk (i + 0)
      (D.homologyMul (D.homogeneousClassOf a) (D.homogeneousClassOf D.homogeneousOne)) =
      GradedMonoid.mk i (D.homogeneousClassOf a)
    apply Sigma.ext (add_zero i)
    apply heq_of_cast_eq (congrArg D.HomologyAt (add_zero i))
    change cast (congrArg D.HomologyAt (add_zero i))
      (D.homogeneousClassOf (D.homogeneousCycleMul a D.homogeneousOne)) =
      D.homogeneousClassOf a
    rw [D.cast_homogeneousClassOf]
    apply congrArg D.homogeneousClassOf
    apply Subtype.ext
    apply Subtype.ext
    all_goals try exact add_zero i
    rw [D.coe_cast_homogeneousCycle]
    simp [homogeneousCycleMul, homogeneousOne]
    all_goals exact add_zero i
  mul_assoc := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    apply Sigma.ext (add_assoc i j k)
    apply heq_of_cast_eq (congrArg D.HomologyAt (add_assoc i j k))
    exact D.homologyMul_assoc x y z

def homogeneousNatCast (D : DGA A 𝒜 dDegree leibnizSign) (n : ℕ) :
    D.HomogeneousCycles 0 :=
  ⟨(n : 𝒜 0), by
    change D.d (n : A) = 0
    rw [← nsmul_one, D.d.map_nsmul, D.d_one, nsmul_zero]⟩

instance homologyGSemiring (D : DGA A 𝒜 dDegree leibnizSign) :
    DirectSum.GSemiring D.HomologyAt where
  natCast n := D.homogeneousClassOf (D.homogeneousNatCast n)
  natCast_zero := by
    apply congrArg D.homogeneousClassOf
    ext
    simp [homogeneousNatCast]
  natCast_succ n := by
    change D.homogeneousClassOf (D.homogeneousNatCast (n + 1)) =
      D.homogeneousClassOf (D.homogeneousNatCast n) +
        D.homogeneousClassOf D.homogeneousOne
    change D.homogeneousClassOf (D.homogeneousNatCast (n + 1)) =
      D.homogeneousClassOf (D.homogeneousNatCast n + D.homogeneousOne)
    apply congrArg D.homogeneousClassOf
    ext
    simp [homogeneousNatCast, homogeneousOne]

def homogeneousIntCast (D : DGA A 𝒜 dDegree leibnizSign) (z : ℤ) :
    D.HomogeneousCycles 0 :=
  ⟨(z : 𝒜 0), by
    change D.d (z : A) = 0
    rw [← zsmul_one, D.d.map_zsmul, D.d_one, zsmul_zero]⟩

instance homologyGRing (D : DGA A 𝒜 dDegree leibnizSign) :
    DirectSum.GRing D.HomologyAt where
  intCast z := D.homogeneousClassOf (D.homogeneousIntCast z)
  intCast_ofNat n := by
    apply congrArg D.homogeneousClassOf
    ext
    simp [homogeneousIntCast, homogeneousNatCast]
  intCast_negSucc_ofNat n := by
    change D.homogeneousClassOf (D.homogeneousIntCast (Int.negSucc n)) =
      -D.homogeneousClassOf (D.homogeneousNatCast (n + 1))
    change D.homogeneousClassOf (D.homogeneousIntCast (Int.negSucc n)) =
      D.homogeneousClassOf (-D.homogeneousNatCast (n + 1))
    apply congrArg D.homogeneousClassOf
    ext
    simp [homogeneousIntCast, homogeneousNatCast]

abbrev GradedHomology (D : DGA A 𝒜 dDegree leibnizSign) :=
  ⨁ i, D.HomologyAt i

def homologyGrading (D : DGA A 𝒜 dDegree leibnizSign) (i : ι) :
    AddSubgroup D.GradedHomology :=
  AddMonoidHom.range (DirectSum.of D.HomologyAt i)

instance homologyGradedMonoid (D : DGA A 𝒜 dDegree leibnizSign) :
    SetLike.GradedMonoid D.homologyGrading where
  one_mem := ⟨GradedMonoid.GOne.one, rfl⟩
  mul_mem i j x y hx hy := by
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    refine ⟨GradedMonoid.GMul.mul a b, ?_⟩
    exact (DirectSum.of_mul_of a b).symm

def homologyGradeEmbed (D : DGA A 𝒜 dDegree leibnizSign) (i : ι) :
    D.HomologyAt i →+ D.homologyGrading i where
  toFun x := ⟨DirectSum.of D.HomologyAt i x, ⟨x, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def homologyDecomposeHom (D : DGA A 𝒜 dDegree leibnizSign) :
    D.GradedHomology →+ ⨁ i, D.homologyGrading i :=
  DirectSum.map D.homologyGradeEmbed

instance homologyDecomposition (D : DGA A 𝒜 dDegree leibnizSign) :
    DirectSum.Decomposition D.homologyGrading where
  decompose' := D.homologyDecomposeHom
  left_inv := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp [homologyDecomposeHom]
    | of i x => simp [homologyDecomposeHom, homologyGradeEmbed]
    | add x y hx hy => simp [map_add, hx, hy]
  right_inv := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp [homologyDecomposeHom]
    | of i x =>
        rcases x with ⟨_, ⟨a, rfl⟩⟩
        simp [homologyDecomposeHom, homologyGradeEmbed]
    | add x y hx hy => simp [map_add, hx, hy]

instance homologyGradedRing (D : DGA A 𝒜 dDegree leibnizSign) :
    GradedRing D.homologyGrading where

end DGA

end KIPBase.SpectralSequence
