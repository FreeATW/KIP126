import KIP126.Def.Steenrod.MilnorCobar.Reindex.Data
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Multiplication.Proofs

/-! # Cochain reindexing and polynomial block embeddings -/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Core.Algebra

@[simp] theorem reindex_rfl {s t : ℕ} (x : cochains s t) : reindex rfl rfl x = x := rfl

theorem reindex_val {s s' t t' : ℕ} (hs : s = s') (ht : t = t') (x : cochains s t) :
    (reindex hs ht x).val = Eq.mp (congrArg TensorPower hs) x.val := by
  subst s'
  subst t'
  rfl

theorem reindex_cup_val {s s' t t' n : ℕ} (h : s + s' = n)
    (x : cochains s t) (y : cochains s' t') :
    (reindex h rfl (cup x y)).val =
      blockRename (n := n) 0 (by omega) x.val * blockRename s (by omega) y.val := by
  subst n
  exact cupPolynomial_blocks x.val y.val

end

end KIP126.Steenrod.Milnor
