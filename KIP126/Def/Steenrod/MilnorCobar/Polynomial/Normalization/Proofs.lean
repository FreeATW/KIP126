import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Grading.Proofs
import Mathlib.Algebra.CharP.Two

/-!
# Augmentation identities for the Milnor coproduct
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Core.Algebra MvPolynomial

/-- Augmenting a renamed slot agrees with renaming after augmentation. -/
theorem augmentSlot_rename {s s' : ℕ} (f : Fin s → Fin s')
    (hf : Function.Injective f) (slot : Fin s) (x : TensorPower s) :
    augmentSlot (f slot) (rename (fun a : Fin s × ℕ => (f a.1, a.2)) x) =
      rename (fun a : Fin s × ℕ => (f a.1, a.2)) (augmentSlot slot x) := by
  have h : (augmentSlot (f slot)).comp (rename (fun a : Fin s × ℕ => (f a.1, a.2))) =
      (rename (fun a : Fin s × ℕ => (f a.1, a.2))).comp (augmentSlot slot) := by
    ext a : 1
    by_cases ha : a.1 = slot <;> simp [augmentSlot, hf.eq_iff, ha]
  exact DFunLike.congr_fun h x

@[simp] theorem augmentSlot_xi_same {s : ℕ} (slot : Fin s) (j : ℕ) :
    augmentSlot slot (xi slot j) = if j = 0 then 1 else 0 := by
  cases j <;> simp [xi, augmentSlot]

theorem augmentSlot_xi_of_ne {s : ℕ} (slot other : Fin s) (h : other ≠ slot) (j : ℕ) :
    augmentSlot slot (xi other j) = xi other j := by
  cases j <;> simp [xi, augmentSlot, h]

/-- The left counit identity on a Milnor generator. -/
theorem augmentSlot_coproduct_left {s : ℕ} (slot : Fin s) (j : ℕ) :
    augmentSlot slot.castSucc (coproductGenerator slot j) = X (slot.succ, j) := by
  have hne : slot.succ ≠ slot.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  simp only [coproductGenerator, map_sum, map_mul, map_pow,
    augmentSlot_xi_same, augmentSlot_xi_of_ne _ _ hne]
  rw [Finset.sum_eq_single (j + 1)]
  · simp [xi]
  · intro i hi hij
    have hi' : i < j + 1 := by have := Finset.mem_range.mp hi; omega
    simp [Nat.sub_ne_zero_of_lt hi']
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

/-- The right counit identity on a Milnor generator. -/
theorem augmentSlot_coproduct_right {s : ℕ} (slot : Fin s) (j : ℕ) :
    augmentSlot slot.succ (coproductGenerator slot j) = X (slot.castSucc, j) := by
  have hne : slot.castSucc ≠ slot.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  simp only [coproductGenerator, map_sum, map_mul, map_pow,
    augmentSlot_xi_same, augmentSlot_xi_of_ne _ _ hne]
  rw [Finset.sum_eq_single 0]
  · simp [xi]
  · intro i hi hi0
    simp [hi0]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

/-- Augmenting a disjoint slot leaves a coproduct generator unchanged. -/
theorem augmentSlot_coproduct_other {s : ℕ} (slot : Fin s) (other : Fin (s + 1))
    (h₁ : slot.castSucc ≠ other) (h₂ : slot.succ ≠ other) (j : ℕ) :
    augmentSlot other (coproductGenerator slot j) = coproductGenerator slot j := by
  simp only [coproductGenerator, map_sum, map_mul, map_pow,
    augmentSlot_xi_of_ne _ _ h₁, augmentSlot_xi_of_ne _ _ h₂]

/-- Left augmentation of a split slot inserts a unit in that slot. -/
theorem augmentSlot_splitSlot_left {s : ℕ} (slot : Fin s) (x : TensorPower s) :
    augmentSlot slot.castSucc (splitSlot slot x) =
      rename (fun a : Fin s × ℕ => (slot.castSucc.succAbove a.1, a.2)) x := by
  have he : (augmentSlot slot.castSucc).comp (splitSlot slot) =
      rename (fun a : Fin s × ℕ => (slot.castSucc.succAbove a.1, a.2)) := by
    ext a : 1
    simp only [AlgHom.comp_apply, splitSlot, aeval_X, rename_X]
    by_cases ha : a.1 = slot
    · simp [ha, augmentSlot_coproduct_left]
    · rw [if_neg ha]
      by_cases hlt : a.1 < slot
      · have hne : a.1.castSucc ≠ slot.castSucc := fun h => ha (Fin.castSucc_injective _ h)
        simp [hlt, augmentSlot, hne, Fin.succAbove_castSucc_of_lt slot a.1 hlt]
      · have hne : a.1.succ ≠ slot.castSucc := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_castSucc] at this
          have := Fin.not_lt.mp hlt
          omega
        simp [hlt, augmentSlot, hne,
          Fin.succAbove_castSucc_of_le slot a.1 (Fin.not_lt.mp hlt)]
  exact DFunLike.congr_fun he x

/-- Right augmentation of a split slot inserts a unit after that slot. -/
theorem augmentSlot_splitSlot_right {s : ℕ} (slot : Fin s) (x : TensorPower s) :
    augmentSlot slot.succ (splitSlot slot x) =
      rename (fun a : Fin s × ℕ => (slot.succ.succAbove a.1, a.2)) x := by
  have he : (augmentSlot slot.succ).comp (splitSlot slot) =
      rename (fun a : Fin s × ℕ => (slot.succ.succAbove a.1, a.2)) := by
    ext a : 1
    simp only [AlgHom.comp_apply, splitSlot, aeval_X, rename_X]
    by_cases ha : a.1 = slot
    · simp [ha, augmentSlot_coproduct_right]
    · rw [if_neg ha]
      by_cases hlt : a.1 < slot
      · have hne : a.1.castSucc ≠ slot.succ := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_castSucc] at this
          omega
        simp [hlt, augmentSlot, hne, Fin.succAbove_succ_of_le slot a.1 (Fin.le_of_lt hlt)]
      · have hgt : slot < a.1 := lt_of_le_of_ne (Fin.not_lt.mp hlt) (Ne.symm ha)
        have hne : a.1.succ ≠ slot.succ := fun h => ha (Fin.succ_injective _ h)
        simp [hlt, augmentSlot, hne, Fin.succAbove_succ_of_lt slot a.1 hgt]
  exact DFunLike.congr_fun he x

/-- Augmentation in an earlier slot commutes with splitting a later slot. -/
theorem augmentSlot_splitSlot_of_lt {s : ℕ} (slot other : Fin s) (hlt : other < slot)
    (x : TensorPower s) :
    augmentSlot other.castSucc (splitSlot slot x) = splitSlot slot (augmentSlot other x) := by
  have he : (augmentSlot other.castSucc).comp (splitSlot slot) =
      (splitSlot slot).comp (augmentSlot other) := by
    ext a : 1
    by_cases ha : a.1 = slot
    · have h₁ : slot.castSucc ≠ other.castSucc := by
        intro h; have := Fin.castSucc_injective _ h; subst other; exact (lt_irrefl _ hlt)
      have h₂ : slot.succ ≠ other.castSucc := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_castSucc] at this
        omega
      have hso : slot ≠ other := ne_of_gt hlt
      simp only [AlgHom.comp_apply, splitSlot, augmentSlot, aeval_X, ha, if_pos,
        hso, if_false]
      exact augmentSlot_coproduct_other slot other.castSucc h₁ h₂ a.2
    · have hiff : (if a.1 < slot then a.1.castSucc else a.1.succ) = other.castSucc ↔ a.1 = other := by
        split_ifs with h
        · exact Fin.castSucc_inj
        · constructor
          · intro heq
            have := congrArg Fin.val heq
            simp only [Fin.val_succ, Fin.val_castSucc] at this
            have := Fin.not_lt.mp h
            omega
          · intro heq; exact (h (heq ▸ hlt)).elim
      by_cases hao : a.1 = other <;>
        simp [AlgHom.comp_apply, splitSlot, augmentSlot, ha, hiff, hao,
          hlt, ne_of_lt hlt]
  exact DFunLike.congr_fun he x

/-- Augmentation in a later slot commutes with splitting an earlier slot. -/
theorem augmentSlot_splitSlot_of_gt {s : ℕ} (slot other : Fin s) (hlt : slot < other)
    (x : TensorPower s) :
    augmentSlot other.succ (splitSlot slot x) = splitSlot slot (augmentSlot other x) := by
  have he : (augmentSlot other.succ).comp (splitSlot slot) =
      (splitSlot slot).comp (augmentSlot other) := by
    ext a : 1
    by_cases ha : a.1 = slot
    · have h₁ : slot.castSucc ≠ other.succ := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_castSucc] at this
        omega
      have h₂ : slot.succ ≠ other.succ := by
        intro h; have := Fin.succ_injective _ h; subst other; exact (lt_irrefl _ hlt)
      have hso : slot ≠ other := ne_of_lt hlt
      simp only [AlgHom.comp_apply, splitSlot, augmentSlot, aeval_X, ha, if_pos,
        hso, if_false]
      exact augmentSlot_coproduct_other slot other.succ h₁ h₂ a.2
    · have hiff : (if a.1 < slot then a.1.castSucc else a.1.succ) = other.succ ↔ a.1 = other := by
        split_ifs with h
        · constructor
          · intro heq
            have := congrArg Fin.val heq
            simp only [Fin.val_succ, Fin.val_castSucc] at this
            omega
          · intro heq; exact (not_lt_of_ge (le_of_lt hlt) (heq ▸ h)).elim
        · exact Fin.succ_inj
      by_cases hao : a.1 = other <;>
        simp [AlgHom.comp_apply, splitSlot, augmentSlot, ha, hiff, hao,
          ne_of_gt hlt, not_lt_of_ge (le_of_lt hlt)]
  exact DFunLike.congr_fun he x

/-- The two adjacent cofaces give the only surviving terms after augmentation. -/
theorem augmentSlot_splitSlot_normalized {s : ℕ} (x : TensorPower s)
    (hx : ∀ slot, augmentSlot slot x = 0) (j : Fin (s + 1)) (i : Fin s) :
    augmentSlot j (splitSlot i x) =
      (if j = i.castSucc then rename (fun a : Fin s × ℕ => (j.succAbove a.1, a.2)) x else 0) +
      (if j = i.succ then rename (fun a : Fin s × ℕ => (j.succAbove a.1, a.2)) x else 0) := by
  by_cases h₁ : j = i.castSucc
  · subst j
    have hne : i.castSucc ≠ i.succ := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_succ] at this; omega
    simp [hne, augmentSlot_splitSlot_left]
  · by_cases h₂ : j = i.succ
    · subst j
      simp [h₁, augmentSlot_splitSlot_right]
    · simp only [if_neg h₁, if_neg h₂, zero_add]
      by_cases hlt : j.val < i.val
      · let k : Fin s := ⟨j.val, lt_trans hlt i.isLt⟩
        have hj : j = k.castSucc := Fin.ext rfl
        rw [hj, augmentSlot_splitSlot_of_lt i k hlt, hx, map_zero]
      · have hji : j.val ≠ i.val := fun h => h₁ (Fin.ext h)
        have hji' : j.val ≠ i.val + 1 := fun h => h₂ (Fin.ext h)
        have hjpos : 0 < j.val := by omega
        let k : Fin s := ⟨j.val - 1, by have := j.isLt; omega⟩
        have hj : j = k.succ := Fin.ext (by dsimp [k]; omega)
        have hk : i < k := by change i.val < j.val - 1; omega
        rw [hj, augmentSlot_splitSlot_of_gt i k hk, hx, map_zero]

/-- Renaming into slots disjoint from the augmented slot is unchanged. -/
theorem augmentSlot_rename_disjoint {s s' : ℕ} (f : Fin s → Fin s') (slot : Fin s')
    (hf : ∀ i, f i ≠ slot) (x : TensorPower s) :
    augmentSlot slot (rename (fun a : Fin s × ℕ => (f a.1, a.2)) x) =
      rename (fun a : Fin s × ℕ => (f a.1, a.2)) x := by
  have he : (augmentSlot slot).comp (rename (fun a : Fin s × ℕ => (f a.1, a.2))) =
      rename (fun a : Fin s × ℕ => (f a.1, a.2)) := by
    ext a : 1
    simp [augmentSlot, hf]
  exact DFunLike.congr_fun he x

/-- Only augmentation at the newly inserted left endpoint survives. -/
theorem augmentSlot_insertLeft_normalized {s : ℕ} (x : TensorPower s)
    (hx : ∀ slot, augmentSlot slot x = 0) (j : Fin (s + 1)) :
    augmentSlot j (insertLeft s x) =
      if j = 0 then rename (fun a : Fin s × ℕ => (j.succAbove a.1, a.2)) x else 0 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa [insertLeft] using augmentSlot_rename_disjoint Fin.succ 0 (fun i => Fin.succ_ne_zero i) x
  · simp only [insertLeft, augmentSlot_rename Fin.succ (Fin.succ_injective s), hx, map_zero,
      Fin.succ_ne_zero, if_false]

/-- Only augmentation at the newly inserted right endpoint survives. -/
theorem augmentSlot_insertRight_normalized {s : ℕ} (x : TensorPower s)
    (hx : ∀ slot, augmentSlot slot x = 0) (j : Fin (s + 1)) :
    augmentSlot j (insertRight s x) =
      if j = Fin.last s then rename (fun a : Fin s × ℕ => (j.succAbove a.1, a.2)) x else 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa [insertRight] using augmentSlot_rename_disjoint Fin.castSucc (Fin.last s)
      (fun i => Fin.castSucc_ne_last i) x
  · simp only [insertRight, augmentSlot_rename Fin.castSucc (Fin.castSucc_injective s), hx, map_zero,
      Fin.castSucc_ne_last, if_false]

/-- The cobar differential preserves the intersection of augmentation kernels. -/
theorem differentialPolynomial_normalized {s : ℕ} (x : TensorPower s)
    (hx : ∀ slot, augmentSlot slot x = 0) (j : Fin (s + 1)) :
    augmentSlot j (differentialPolynomial s x) = 0 := by
  classical
  let q := rename (fun a : Fin s × ℕ => (j.succAbove a.1, a.2)) x
  have hleft : (if j = 0 then q else 0) + ∑ i : Fin s, (if j = i.succ then q else 0) = q := by
    rw [← Fin.sum_univ_succ (fun k : Fin (s + 1) => if j = k then q else 0)]
    simp
  have hright : (∑ i : Fin s, (if j = i.castSucc then q else 0)) +
      (if j = Fin.last s then q else 0) = q := by
    rw [← Fin.sum_univ_castSucc (fun k : Fin (s + 1) => if j = k then q else 0)]
    simp
  simp only [differentialPolynomial, LinearMap.add_apply, LinearMap.sum_apply,
    AlgHom.toLinearMap_apply, map_add, map_sum,
    augmentSlot_insertLeft_normalized x hx, augmentSlot_insertRight_normalized x hx,
    augmentSlot_splitSlot_normalized x hx, Finset.sum_add_distrib]
  change (if j = 0 then q else 0) + (if j = Fin.last s then q else 0) +
    ((∑ i : Fin s, if j = i.castSucc then q else 0) +
      ∑ i : Fin s, if j = i.succ then q else 0) = 0
  calc
    _ = ((∑ i : Fin s, if j = i.castSucc then q else 0) + (if j = Fin.last s then q else 0)) +
        ((if j = 0 then q else 0) + ∑ i : Fin s, if j = i.succ then q else 0) := by abel
    _ = q + q := by rw [hleft, hright]
    _ = 0 := CharTwo.add_self_eq_zero q

end

end KIP126.Steenrod.Milnor
