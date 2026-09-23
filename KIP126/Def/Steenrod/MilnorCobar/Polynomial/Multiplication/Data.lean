import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Data

/-! # Embedding a block of tensor slots -/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Core.Algebra

/-- Embed a block of `s` slots starting at `offset` in `n` slots. -/
def blockRename {s n : ℕ} (offset : ℕ) (h : offset + s ≤ n) :
    TensorPower s →ₐ[F2] TensorPower n :=
  MvPolynomial.rename fun a => (⟨offset + a.1.val, by have := a.1.isLt; omega⟩, a.2)

end

end KIP126.Steenrod.Milnor
