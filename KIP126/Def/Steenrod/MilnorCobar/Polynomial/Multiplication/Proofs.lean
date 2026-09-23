import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Multiplication.Data

/-!
# Naturality and the Leibniz identity for cobar concatenation
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Core.Algebra MvPolynomial

/-- Slot renaming respects the convention `ξ₀ = 1`. -/
theorem rename_xi {s s' : ℕ} (f : Fin s → Fin s') (i : Fin s) (j : ℕ) :
    rename (fun a : Fin s × ℕ => (f a.1, a.2)) (xi i j) = xi (f i) j := by
  cases j <;> simp [xi]

/-- A coproduct depends only on the two adjacent slots into which it lands. -/
theorem rename_coproductGenerator {s s' : ℕ} (g : Fin (s + 1) → Fin (s' + 1))
    (i : Fin s) (k : Fin s') (h₁ : g i.castSucc = k.castSucc) (h₂ : g i.succ = k.succ)
    (j : ℕ) :
    rename (fun a : Fin (s + 1) × ℕ => (g a.1, a.2)) (coproductGenerator i j) =
      coproductGenerator k j := by
  simp only [coproductGenerator, map_sum, map_mul, map_pow, rename_xi, h₁, h₂]

/-- Naturality of splitting with respect to an embedding of tensor slots. -/
theorem splitSlot_rename {s s' : ℕ} (f : Fin s → Fin s')
    (g : Fin (s + 1) → Fin (s' + 1)) (i : Fin s) (k : Fin s')
    (hf : ∀ a, f a = k ↔ a = i)
    (h₁ : g i.castSucc = k.castSucc) (h₂ : g i.succ = k.succ)
    (hg : ∀ a, a ≠ i →
      g (if a < i then a.castSucc else a.succ) =
        if f a < k then (f a).castSucc else (f a).succ)
    (x : TensorPower s) :
    splitSlot k (rename (fun a : Fin s × ℕ => (f a.1, a.2)) x) =
      rename (fun a : Fin (s + 1) × ℕ => (g a.1, a.2)) (splitSlot i x) := by
  have he : (splitSlot k).comp (rename (fun a : Fin s × ℕ => (f a.1, a.2))) =
      (rename (fun a : Fin (s + 1) × ℕ => (g a.1, a.2))).comp (splitSlot i) := by
    ext a : 1
    simp only [AlgHom.comp_apply, rename_X, splitSlot, aeval_X, hf]
    by_cases ha : a.1 = i
    · simp only [if_pos ha]
      exact (rename_coproductGenerator g i k h₁ h₂ a.2).symm
    · simp only [if_neg ha, rename_X, hg a.1 ha]
  exact DFunLike.congr_fun he x

/-- Splitting a slot outside an embedded tensor block only reindexes the block. -/
theorem splitSlot_rename_disjoint {s s' : ℕ} (f : Fin s → Fin s')
    (g : Fin s → Fin (s' + 1)) (k : Fin s')
    (hf : ∀ a, f a ≠ k)
    (hg : ∀ a, (if f a < k then (f a).castSucc else (f a).succ) = g a)
    (x : TensorPower s) :
    splitSlot k (rename (fun a : Fin s × ℕ => (f a.1, a.2)) x) =
      rename (fun a : Fin s × ℕ => (g a.1, a.2)) x := by
  have he : (splitSlot k).comp (rename (fun a : Fin s × ℕ => (f a.1, a.2))) =
      rename (fun a : Fin s × ℕ => (g a.1, a.2)) := by
    ext a : 1
    simp [splitSlot, hf, hg]
  exact DFunLike.congr_fun he x

/-- Concatenation embeds the two factors in consecutive tensor blocks. -/
theorem cupPolynomial_blocks {s s' : ℕ} (x : TensorPower s) (y : TensorPower s') :
    cupPolynomial x y = blockRename 0 (by omega) x * blockRename s (by omega) y := by
  simp only [cupPolynomial, blockRename]
  congr 1
  congr 2
  funext a
  exact Prod.ext (Fin.ext (by simp)) rfl

/-- Composition adds the starting positions of embedded blocks. -/
theorem blockRename_comp {s m n : ℕ} (a b : ℕ) (ha : a + s ≤ m) (hb : b + m ≤ n)
    (x : TensorPower s) :
    blockRename b hb (blockRename a ha x) = blockRename (b + a) (by omega) x := by
  simp only [blockRename, rename_rename]
  congr 2
  funext i
  apply Prod.ext
  · apply Fin.ext
    dsimp
    omega
  · rfl

theorem insertLeft_blockRename {s n : ℕ} (a : ℕ) (ha : a + s ≤ n) (x : TensorPower s) :
    insertLeft n (blockRename a ha x) = blockRename (a + 1) (by omega) x := by
  simp only [insertLeft, blockRename, rename_rename]
  congr 2
  funext i
  apply Prod.ext
  · apply Fin.ext
    dsimp
    omega
  · rfl

theorem insertRight_blockRename {s n : ℕ} (a : ℕ) (ha : a + s ≤ n) (x : TensorPower s) :
    insertRight n (blockRename a ha x) = blockRename a (by omega) x := by
  simp only [insertRight, blockRename, rename_rename]
  rfl

theorem blockRename_insertLeft {s n : ℕ} (a : ℕ) (ha : a + (s + 1) ≤ n) (x : TensorPower s) :
    blockRename a ha (insertLeft s x) = blockRename (a + 1) (by omega) x := by
  simp only [insertLeft, blockRename, rename_rename]
  congr 2
  funext i
  apply Prod.ext
  · apply Fin.ext
    dsimp
    omega
  · rfl

theorem blockRename_insertRight {s n : ℕ} (a : ℕ) (ha : a + (s + 1) ≤ n) (x : TensorPower s) :
    blockRename a ha (insertRight s x) = blockRename a (by omega) x := by
  simp only [insertRight, blockRename, rename_rename]
  rfl

/-- A coproduct taken inside an embedded block splits that block. -/
theorem splitSlot_blockRename_inside {s n : ℕ} (a : ℕ) (ha : a + s ≤ n)
    (i : Fin s) (x : TensorPower s) :
    splitSlot (⟨a + i.val, by have := i.isLt; omega⟩ : Fin n) (blockRename a ha x) =
      blockRename a (by omega) (splitSlot i x) := by
  refine splitSlot_rename
    (fun j : Fin s => (⟨a + j.val, by have := j.isLt; omega⟩ : Fin n))
    (fun j : Fin (s + 1) => (⟨a + j.val, by have := j.isLt; omega⟩ : Fin (n + 1)))
    i ⟨a + i.val, by have := i.isLt; omega⟩ ?_ ?_ ?_ ?_ x
  · intro j
    simp only [Fin.ext_iff]
    omega
  · apply Fin.ext; rfl
  · apply Fin.ext; dsimp; omega
  · intro j hj
    have hlt : (⟨a + j.val, by have := j.isLt; omega⟩ : Fin n) <
        ⟨a + i.val, by have := i.isLt; omega⟩ ↔ j < i := by
      change a + j.val < a + i.val ↔ j.val < i.val
      omega
    simp only [hlt]
    split_ifs
    · apply Fin.ext; rfl
    · apply Fin.ext; dsimp; omega

/-- A coproduct preceding a block shifts the whole block one slot to the right. -/
theorem splitSlot_blockRename_before {s n : ℕ} (a : ℕ) (ha : a + s ≤ n)
    (i : Fin n) (hi : i.val < a) (x : TensorPower s) :
    splitSlot i (blockRename a ha x) = blockRename (a + 1) (by omega) x := by
  refine splitSlot_rename_disjoint
    (fun j : Fin s => (⟨a + j.val, by have := j.isLt; omega⟩ : Fin n))
    (fun j : Fin s => (⟨a + 1 + j.val, by have := j.isLt; omega⟩ : Fin (n + 1)))
    i ?_ ?_ x
  · intro j h
    have := congrArg Fin.val h
    dsimp at this
    omega
  · intro j
    have h : ¬(⟨a + j.val, by have := j.isLt; omega⟩ : Fin n) < i := by
      change ¬a + j.val < i.val
      omega
    rw [if_neg h]
    apply Fin.ext
    dsimp
    omega

/-- A coproduct following a block leaves its position unchanged. -/
theorem splitSlot_blockRename_after {s n : ℕ} (a : ℕ) (ha : a + s ≤ n)
    (i : Fin n) (hi : a + s ≤ i.val) (x : TensorPower s) :
    splitSlot i (blockRename a ha x) = blockRename a (by omega) x := by
  refine splitSlot_rename_disjoint
    (fun j : Fin s => (⟨a + j.val, by have := j.isLt; omega⟩ : Fin n))
    (fun j : Fin s => (⟨a + j.val, by have := j.isLt; omega⟩ : Fin (n + 1)))
    i ?_ ?_ x
  · intro j h
    have := congrArg Fin.val h
    have := j.isLt
    dsimp at *
    omega
  · intro j
    have h : (⟨a + j.val, by have := j.isLt; omega⟩ : Fin n) < i := by
      change a + j.val < i.val
      have := j.isLt
      omega
    rw [if_pos h]
    rfl

/-- The characteristic-two Leibniz formula, with all terms embedded in the
same tensor power so that no associativity casts are implicit. -/
theorem differentialPolynomial_cup_blocks {s s' : ℕ} (x : TensorPower s) (y : TensorPower s') :
    differentialPolynomial (s + s') (cupPolynomial x y) =
      blockRename (n := s + s' + 1) 0 (by omega) (differentialPolynomial s x) *
        blockRename (s + 1) (by omega) y +
      blockRename 0 (by omega) x *
        blockRename s (by omega) (differentialPolynomial s' y) := by
  have hLL (i : Fin s) :
      splitSlot (i.castAdd s') (blockRename (n := s + s') 0 (by omega) x) =
        blockRename 0 (by omega) (splitSlot i x) := by
    have hk : (⟨0 + i.val, by have := i.isLt; omega⟩ : Fin (s + s')) = i.castAdd s' :=
      Fin.ext (by simp)
    simpa only [hk] using splitSlot_blockRename_inside 0 (by omega : 0 + s ≤ s + s') i x
  have hLR (i : Fin s) :
      splitSlot (i.castAdd s') (blockRename (n := s + s') s (by omega) y) =
        blockRename (s + 1) (by omega) y :=
    splitSlot_blockRename_before s (by omega) (i.castAdd s') i.isLt y
  have hRL (i : Fin s') :
      splitSlot (i.natAdd s) (blockRename (n := s + s') 0 (by omega) x) =
        blockRename 0 (by omega) x :=
    splitSlot_blockRename_after 0 (by omega) (i.natAdd s) (by dsimp; omega) x
  have hRR (i : Fin s') :
      splitSlot (i.natAdd s) (blockRename (n := s + s') s (by omega) y) =
        blockRename s (by omega) (splitSlot i y) :=
    splitSlot_blockRename_inside s (by omega) i y
  rw [cupPolynomial_blocks]
  simp only [differentialPolynomial, LinearMap.add_apply, LinearMap.sum_apply,
    AlgHom.toLinearMap_apply, map_add, map_sum, map_mul,
    insertLeft_blockRename, insertRight_blockRename, blockRename_insertLeft,
    blockRename_insertRight, Fin.sum_univ_add, hLL, hLR, hRL, hRR,
    add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
  abel_nf
  simp [CharTwo.two_eq_zero]

end

end KIP126.Steenrod.Milnor
