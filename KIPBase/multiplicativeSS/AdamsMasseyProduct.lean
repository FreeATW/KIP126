import KIPBase.multiplicativeSS.AdamsEnriched

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

namespace AdamsPageMasseyProduct

noncomputable abbrev E (X Y : FiniteSpectra 𝒮) :
    SpectralSequence (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ) :=
  adamsMappingSS X.1 Y.1

/-- The degree of a triple Massey product on `E_r`, computed using the
differential on `E_(r-1)`. -/
def degree (r : ℤ) (i j k : ℤ × ℤ) : ℤ × ℤ :=
  i + j + k - adamsDiffDeg (r - 1)

/-- Transport a page element along equalities of its page and homogeneous
degree. -/
noncomputable def pageCast (X Y : FiniteSpectra 𝒮) {r r' : ℤ}
    {i i' : ℤ × ℤ} (hr : r = r') (hi : i = i')
    (x : (E X Y).Page r i) : (E X Y).Page r' i' := by
  subst r'
  subst i'
  exact x

/-- Cycles of degree `k` on page `s`. -/
noncomputable abbrev Cycles (X Y : FiniteSpectra 𝒮) (s : ℤ) (k : ℤ × ℤ) :=
  ((E X Y).pageShortComplex s (k - (E X Y).diffDeg s)).cycles

/-- The page element represented by a cycle. -/
noncomputable def cycleValue (X Y : FiniteSpectra 𝒮) (s : ℤ) (k : ℤ × ℤ)
    (a : Cycles X Y s k) : (E X Y).Page s k :=
  (((E X Y).pageShortComplex s (k - (E X Y).diffDeg s)).iCycles ≫
    ((E X Y).pageShortComplexCenterIso s k).hom) a

/-- The `E_r` class represented by an `E_(r-1)` cycle.  The construction
uses `pageHomologyIso (r - 1)`, which requires the source page `r - 1` to
be at least the initial page `r₀ = 2`; hence `3 ≤ r`. -/
noncomputable def classOfCycle (X Y : FiniteSpectra 𝒮) (r : ℤ) (hr : 3 ≤ r)
    (k : ℤ × ℤ) (a : Cycles X Y (r - 1) k) : (E X Y).Page r k :=
  pageCast X Y (by omega) rfl
    (((E X Y).pageHomologyIso (r - 1) k (by
        show (E X Y).r₀ ≤ r - 1
        rw [adamsMappingSS_r₀]
        omega)).inv
      (((E X Y).pageShortComplex (r - 1)
        (k - (E X Y).diffDeg (r - 1))).homologyπ a))

/-- Composition of two homogeneous page elements. -/
noncomputable def comp (X Y Z : FiniteSpectra 𝒮) (s : ℤ)
    (i j : ℤ × ℤ) (a : (E X Y).Page s i) (b : (E Y Z).Page s j) :
    (E X Z).Page s (i + j) :=
  (adamsCompositionConvergingSSPairing X.1 Y.1 Z.1 X.2 Y.2 Z.2).ssPairing.pair
    s i j (a ⊗ₜ b)

/-- The differential of an element in degree `i + j - diffDeg s`, reindexed
to degree `i + j`. -/
noncomputable def definingDifferential (X Y : FiniteSpectra 𝒮) (s : ℤ)
    (i j : ℤ × ℤ)
    (y : (E X Y).Page s (i + j - adamsDiffDeg s)) :
    (E X Y).Page s (i + j) :=
  pageCast X Y rfl (by
      rw [adamsMappingSS_diffDeg]
      abel)
    ((E X Y).d s (i + j - adamsDiffDeg s) y)

/-- The first summand `y * c` in a defining system, transported to the
Massey-product degree. -/
noncomputable def leftTerm (X Y Z : FiniteSpectra 𝒮) (s : ℤ)
    (i j k : ℤ × ℤ)
    (y : (E X Y).Page s (i + j - adamsDiffDeg s))
    (c : (E Y Z).Page s k) :
    (E X Z).Page s (i + j + k - adamsDiffDeg s) :=
  pageCast X Z rfl (by abel)
    (comp X Y Z s (i + j - adamsDiffDeg s) k y c)

/-- The second summand `a * z` in a defining system, transported to the
Massey-product degree. -/
noncomputable def rightTerm (X Y Z : FiniteSpectra 𝒮) (s : ℤ)
    (i j k : ℤ × ℤ)
    (a : (E X Y).Page s i)
    (z : (E Y Z).Page s (j + k - adamsDiffDeg s)) :
    (E X Z).Page s (i + j + k - adamsDiffDeg s) :=
  pageCast X Z rfl (by abel)
    (comp X Y Z s i (j + k - adamsDiffDeg s) a z)

/-- The homogeneous triple Massey-product relation on the `E_r`-page of the
mapping Adams spectral sequences, for `r ≥ 3` (so that the defining
differential on `E_(r-1)` is an Adams-page differential: the source page
`r - 1 ≥ r₀ = 2`).

The witnesses `y` and `z` live on `E_(r-1)` and satisfy
`d y = a b` and `d z = b c`.  The sign is the one forced by the parity in
the Leibniz rule: the second term is `a z` in odd parity and `-a z` in even
parity. -/
def Relation (r : ℤ) (hr : 3 ≤ r) {W X Y Z : FiniteSpectra 𝒮}
    {i j k : ℤ × ℤ}
    (x : (E W Z).Page r (degree r i j k))
    (a : (E W X).Page r i) (b : (E X Y).Page r j)
    (c : (E Y Z).Page r k) : Prop :=
  ∃ (a' : Cycles W X (r - 1) i) (b' : Cycles X Y (r - 1) j)
      (c' : Cycles Y Z (r - 1) k)
      (x' : Cycles W Z (r - 1) (degree r i j k))
      (y : (E W Y).Page (r - 1) (i + j - adamsDiffDeg (r - 1)))
      (z : (E X Z).Page (r - 1) (j + k - adamsDiffDeg (r - 1))),
    classOfCycle W X r hr i a' = a ∧
    classOfCycle X Y r hr j b' = b ∧
    classOfCycle Y Z r hr k c' = c ∧
    classOfCycle W Z r hr (degree r i j k) x' = x ∧
    definingDifferential W Y (r - 1) i j y =
      comp W X Y (r - 1) i j (cycleValue W X (r - 1) i a')
        (cycleValue X Y (r - 1) j b') ∧
    definingDifferential X Z (r - 1) j k z =
      comp X Y Z (r - 1) j k (cycleValue X Y (r - 1) j b')
        (cycleValue Y Z (r - 1) k c') ∧
    cycleValue W Z (r - 1) (degree r i j k) x' =
      leftTerm W Y Z (r - 1) i j k y (cycleValue Y Z (r - 1) k c') +
        if (adamsCompositionConvergingSSPairing W.1 X.1 Y.1 W.2 X.2 Y.2).ssPairing.parity i = 1 then
          rightTerm W X Z (r - 1) i j k (cycleValue W X (r - 1) i a') z
        else
          -rightTerm W X Z (r - 1) i j k (cycleValue W X (r - 1) i a') z

end AdamsPageMasseyProduct

end KIPBase.StableHomotopy
