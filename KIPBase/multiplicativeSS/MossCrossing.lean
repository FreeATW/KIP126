import KIPBase.multiplicativeSS.AdamsMasseyProduct

/-!
# Moss crossing for mapping Adams spectral sequences

These predicates use the Moss direction, **opposite** to
`SpectralSequence.Crossing.NoCrossing`: a crossing differential starts at a
*lower* filtration than the possible `d_(r-1)` preimage of a product and ends
at a *higher* filtration than that product.

The Adams bidegree is `(filtration, total degree)` and `d_m` has degree
`(m, m-1)`. Thus a product in bidegree `k` has stem `k.2 - k.1`; a crossing
source at filtration `q` has bidegree `(q, q + (k.2 - k.1) + 1)`.
-/

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

namespace MossCrossing

/-- The bidegree in stem one above `k` and filtration `q`. -/
def sourceDegree (k : ℤ × ℤ) (q : ℤ) : ℤ × ℤ :=
  (q, q + (k.2 - k.1) + 1)

/-- A Moss crossing for a product of degree `k` on `E_r`.

The defining systems for an `E_r` Massey product use `d_(r-1)`. A crossing
is a nonzero later differential `d_m`, `m > r`, whose source filtration `q`
is nonnegative and strictly below `k.1 - (r-1)`, while its target filtration
`q+m` is strictly above `k.1`. Its source stem is one greater than the
product stem. -/
def Exists (X Y : FiniteSpectra 𝒮) (r : ℤ) (k : ℤ × ℤ) : Prop :=
  ∃ m q : ℤ,
    r < m ∧
    0 ≤ q ∧
    q < k.1 - (r - 1) ∧
    k.1 < q + m ∧
    (AdamsPageMasseyProduct.E X Y).d m (sourceDegree k q) ≠ 0

/-- No Moss crossing in the bidegree of a product on `E_r`. -/
def None (X Y : FiniteSpectra 𝒮) (r : ℤ) (k : ℤ × ℤ) : Prop :=
  ¬ Exists X Y r k

/-- The two non-crossing hypotheses for an `E_r` triple Massey product
`⟨a,b,c⟩`. They concern `ab` in `E(W,Y)` and `bc` in `E(X,Z)`, respectively. -/
def ForProducts (r : ℤ) {W X Y Z : FiniteSpectra 𝒮}
    (i j k : ℤ × ℤ) : Prop :=
  None W Y r (i + j) ∧
  None X Z r (j + k)

end MossCrossing

end KIPBase.StableHomotopy
