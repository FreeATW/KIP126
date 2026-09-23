import KIPBase.Mathlib

namespace KIPBase.SpectralSequence

universe u v w

variable {R : Type u} [Ring R]
variable {ι : Type v} [DecidableEq ι] [AddMonoid ι]
variable {σ : Type w} [SetLike σ R] [AddSubmonoidClass σ R]

class TodaBracket (𝒜 : ι → σ) [GradedRing 𝒜]
    (bracketGrading : ι → ι → ι → ι)
    (jugglingSign : ι → ι → ι → ι → R) where
  juggling_grading : ∀ j k l m : ι,
    bracketGrading j k l + m = j + bracketGrading k l m
  juggling_sign : ∀ i j k l : ι,
    jugglingSign i j k l = 1 ∨ jugglingSign i j k l = -1
  relation : ∀ {i j k l : ι} {x a b c : R},
    x ∈ 𝒜 i → a ∈ 𝒜 j → b ∈ 𝒜 k → c ∈ 𝒜 l → Prop
  composable : ∀ {i j k l : ι} {x a b c : R}
    {hx : x ∈ 𝒜 i} {ha : a ∈ 𝒜 j} {hb : b ∈ 𝒜 k} {hc : c ∈ 𝒜 l},
    relation hx ha hb hc →
    a * b = 0 ∧ b * c = 0
  grading_axiom : ∀ {i j k l : ι} {x a b c : R}
    {hx : x ∈ 𝒜 i} {ha : a ∈ 𝒜 j} {hb : b ∈ 𝒜 k} {hc : c ∈ 𝒜 l},
    relation hx ha hb hc → i = bracketGrading j k l
  indeterminacy_left : ∀ {i j k l m : ι} {x a b c y : R}
    {hx : x ∈ 𝒜 i} {ha : a ∈ 𝒜 j} {hb : b ∈ 𝒜 k} {hc : c ∈ 𝒜 l},
    relation hx ha hb hc → (hdegree : i = j + m) → (hy : y ∈ 𝒜 m) →
    relation (by
      rw [hdegree] at hx
      exact add_mem hx (SetLike.mul_mem_graded ha hy)) ha hb hc
  indeterminacy_right : ∀ {i j k l m : ι} {x a b c y : R}
    {hx : x ∈ 𝒜 i} {ha : a ∈ 𝒜 j} {hb : b ∈ 𝒜 k} {hc : c ∈ 𝒜 l},
    relation hx ha hb hc → (hdegree : i = m + l) → (hy : y ∈ 𝒜 m) →
    relation (by
      rw [hdegree] at hx
      exact add_mem hx (SetLike.mul_mem_graded hy hc)) ha hb hc
  indeterminacy_complete : ∀ {i j k l : ι} {x₁ x₂ a b c : R}
    {hx₁ : x₁ ∈ 𝒜 i} {hx₂ : x₂ ∈ 𝒜 i}
    {ha : a ∈ 𝒜 j} {hb : b ∈ 𝒜 k} {hc : c ∈ 𝒜 l},
    relation hx₁ ha hb hc → relation hx₂ ha hb hc →
    ∃ (m n : ι) (y z : R), y ∈ 𝒜 m ∧ z ∈ 𝒜 n ∧
      i = j + m ∧ i = n + l ∧ x₁ - x₂ = a * y + z * c
  juggling : ∀ {i j k l m : ι} {x a b c d : R}
    {hx : x ∈ 𝒜 i} {ha : a ∈ 𝒜 j} {hb : b ∈ 𝒜 k} {hc : c ∈ 𝒜 l}
    {hd : d ∈ 𝒜 m}, relation hx ha hb hc → c * d = 0 →
    ∃ y : R, ∃ hy : y ∈ 𝒜 (bracketGrading k l m),
      relation hy hb hc hd ∧ x * d = jugglingSign i j k l * (a * y)
  exists_relation : ∀ {j k l : ι} {a b c : R}
    (ha : a ∈ 𝒜 j) (hb : b ∈ 𝒜 k) (hc : c ∈ 𝒜 l),
    a * b = 0 → b * c = 0 →
    ∃ x : R, ∃ hx : x ∈ 𝒜 (bracketGrading j k l), relation hx ha hb hc

end KIPBase.SpectralSequence
