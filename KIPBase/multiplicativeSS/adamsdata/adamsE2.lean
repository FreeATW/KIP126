import KIPBase.StableHomotopy.Adams

namespace KIPBase.StableHomotopy

universe u v

/-- The prime for this Adams `E₂` data is fixed at `2`. -/
def AdamsE2Prime : ℕ := 2

/-- The classes `hᵢ` on the Adams `E₂`-page of the sphere, in bidegree
`(s, t) = (1, 2^i)` at the fixed prime `2`. Their values and the
one-dimensionality of these components are supplied as external data. -/
class AdamsE2Data (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮] where
  hi : ∀ i : ℕ,
    (AdamsSS.{u, v} 𝒮 (SphereSpectrum (𝒮 := 𝒮))).Page 2
      (1, (AdamsE2Prime : ℤ) ^ i)
  hi_ne_zero : ∀ i : ℕ, hi i ≠ 0
  at_most_one_nonzero : ∀ (i : ℕ)
      (x y : (AdamsSS.{u, v} 𝒮 (SphereSpectrum (𝒮 := 𝒮))).Page 2
        (1, (AdamsE2Prime : ℤ) ^ i)),
    x ≠ 0 → y ≠ 0 → x = y

/-- Every nonzero class in this bidegree is the specified `hᵢ`. -/
theorem AdamsE2Data.eq_hi_of_ne_zero {𝒮 : Type u}
    [StableHomotopyCategory.{u, v} 𝒮] [AdamsE2Data.{u, v} 𝒮]
    (i : ℕ)
    (x : (AdamsSS.{u, v} 𝒮 (SphereSpectrum (𝒮 := 𝒮))).Page 2
      (1, (AdamsE2Prime : ℤ) ^ i)) (hx : x ≠ 0) :
    x = AdamsE2Data.hi i :=
  AdamsE2Data.at_most_one_nonzero (𝒮 := 𝒮) i x (AdamsE2Data.hi i) hx
    (AdamsE2Data.hi_ne_zero i)

end KIPBase.StableHomotopy
