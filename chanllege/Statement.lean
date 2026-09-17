import chanllege.Adams

/-!
Target: Lin--Wang--Xu, *On the Last Kervaire Invariant Problem*,
target.pdf, Theorem 1.4 (= Theorem 7.1), PDF page 2.

The statement is closed: it has no model, differential, table, or survival
hypotheses. Existence of the geometric realization is part of the conclusion,
so the universal clause cannot be discharged by making its domain empty.
-/

namespace KervaireChallenge

/-- `h₆² ∈ E₂^(2,128)(S⁰)` survives as a nonzero `E∞` class in the
classical mod-2 Adams spectral sequence. The stem is `128 - 2 = 126`.

Quantification over geometric Adams resolutions makes the result independent
of choices of resolution and point-set presentations. `IsH6Squared` uses the
unique-nonzero-class characterization in this particular bidegree. -/
def H6SquaredSurvivesToEInfinity : Prop :=
  Nonempty ClassicalAdamsSphere ∧
    ∀ A : ClassicalAdamsSphere, ∃ x : A.E₂ 2 128,
      A.IsH6Squared x ∧ A.SurvivesToEInfinity x

end KervaireChallenge
