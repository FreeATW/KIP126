import KIP126.Def.ClassicalAdams.Tower.Data

/-! # Composition laws for the constructed Adams tower -/

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

@[simp] theorem adamsTowerMap_self (s : ℕ) :
    adamsTowerMap unit X s s le_rfl = 𝟙 _ := by
  apply eq_of_heq
  unfold adamsTowerMap
  rw [eqToHom_comp_heq_iff, Nat.sub_self]
  rfl

theorem adamsTowerMap_succ (s t : ℕ) (h : s ≤ t) :
    adamsTowerMap unit X s (t + 1) (by omega) =
      adamsTowerStep unit X t ≫ adamsTowerMap unit X s t h := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  apply eq_of_heq
  simp only [adamsTowerMap, eqToHom_comp_heq_iff]
  have h : adamsTowerComposite unit X s (s + n + 1 - s) ≍
      adamsTowerStep unit X (s + n) ≫ adamsTowerComposite unit X s n := by
    have hn : s + n + 1 - s = n + 1 := by omega
    rw [hn]
    rfl
  apply h.trans
  apply CategoryTheory.heq_comp rfl rfl rfl (HEq.rfl)
  symm
  rw [eqToHom_comp_heq_iff, Nat.add_sub_cancel_left]

theorem adamsTowerMap_comp (s t z : ℕ) (hst : s ≤ t) (htz : t ≤ z) :
    adamsTowerMap unit X t z htz ≫ adamsTowerMap unit X s t hst =
      adamsTowerMap unit X s z (by omega) := by
  induction z, htz using Nat.le_induction with
  | base => simp
  | succ z htz ih =>
    rw [adamsTowerMap_succ unit X t z htz,
      adamsTowerMap_succ unit X s z (by omega), Category.assoc, ih]

@[simp] theorem adamsTowerMapAt_self (s : ℤ) :
    adamsTowerMapAt unit X s s le_rfl = 𝟙 _ :=
  adamsTowerMap_self unit X s.toNat

theorem adamsTowerMapAt_comp (s t z : ℤ) (hst : s ≤ t) (htz : t ≤ z) :
    adamsTowerMapAt unit X t z htz ≫ adamsTowerMapAt unit X s t hst =
      adamsTowerMapAt unit X s z (by omega) :=
  adamsTowerMap_comp unit X s.toNat t.toNat z.toNat (by omega) (by omega)

end KIP126.Classical.Adams
