import KIP126.Def.ClassicalAdams.SphereSequence.Data

/-!
# The generalized Leibniz rule (Theorem 6.1)

The operations below are an explicit page-level interface.  A concrete
extension spectral sequence supplies these operations and its crossing
predicates; this file states the theorem over that typed input and does not
assert the open propagation result.
-/
namespace KIP126.Solution.Tools.Thm6_1Leibniz

open KIP126.Classical.Adams

abbrev Degree := Bidegree

def shift (r : ℤ) : Degree := (r, r - 1)
def targetDegree (r : ℤ) (b : Degree) : Degree := b + shift r

/-- Page elements, permanent representatives, normalized extensions, and
crossing predicates for a fixed normalized map. -/
structure Operations where
  Map : Type
  e : Map → ℤ
  SourceCycle : ℤ → Degree → Type
  TargetCycle : ℤ → Degree → Type
  SourcePermanent : Degree → Type
  TargetPermanent : Degree → Type
  sourceDifferential : ∀ (r : ℤ) (b : Degree),
    SourceCycle (r - 1) b → SourcePermanent (targetDegree r b)
  targetDifferential : ∀ (r page : ℤ) (b : Degree),
    TargetCycle page b → TargetPermanent (targetDegree r b)
  finiteExtension : ∀ (f : Map) (page length : ℤ)
    (sourcePage : ℤ) (sourceDegree : Degree)
    (targetPage : ℤ) (targetDegree' : Degree),
    SourceCycle sourcePage sourceDegree →
      TargetCycle targetPage targetDegree' → Prop
  infiniteExtension : ∀ (f : Map) (length : ℤ)
    (sourceDegree targetDegree' : Degree),
    SourcePermanent sourceDegree → TargetPermanent targetDegree' → Prop
  sourceNoCrossing : ∀ (f : Map) (page : ℤ)
    (sourcePage : ℤ) (sourceDegree targetDegree' : Degree),
    SourceCycle sourcePage sourceDegree → SourcePermanent targetDegree' → Prop
  finiteNoCrossing : ∀ (f : Map) (page length : ℤ)
    (sourcePage targetPage : ℤ) (sourceDegree targetDegree' : Degree),
    SourceCycle sourcePage sourceDegree → TargetCycle targetPage targetDegree' → Prop
  infiniteNoCrossing : ∀ (f : Map) (length : ℤ)
    (sourceDegree targetDegree' : Degree),
    SourcePermanent sourceDegree → TargetPermanent targetDegree' → Prop

/-- One exact instance of the hypotheses in Theorem 6.1. -/
structure Input (O : Operations) where
  f : O.Map
  n : ℤ
  r : ℤ
  m : ℤ
  l : ℤ
  e : ℤ
  s : ℤ
  t : ℤ
  e_eq : O.e f = e
  bounds : 2 ≤ n ∧ n ≤ r ∧ e ≤ m ∧ m ≤ n - 2 + e ∧ e ≤ l
  x : O.SourceCycle (r - 1) (s, t)
  y : O.TargetCycle (r - 1 - m + e) (s + m, t + m)
  xInfinity : O.SourcePermanent (targetDegree r (s, t))
  yInfinity : O.TargetPermanent
    (targetDegree l (targetDegree r (s, t)))
  firstDifferential : O.sourceDifferential r (s, t) x = xInfinity
  finiteExtension : O.finiteExtension f n m (r - 1) (s, t)
    (r - 1 - m + e) (s + m, t + m) x y
  infiniteExtension : O.infiniteExtension f l (targetDegree r (s, t))
    (targetDegree l (targetDegree r (s, t))) xInfinity yInfinity
  noCrossing :
    O.sourceNoCrossing f n (r - 1) (s, t) (targetDegree r (s, t)) x xInfinity ∨
      O.finiteNoCrossing f n m (r - 1) (r - 1 - m + e)
        (s, t) (s + m, t + m)
        x y
  targetNoCrossing : O.infiniteNoCrossing f l
    (targetDegree r (s, t)) (targetDegree l (targetDegree r (s, t)))
      xInfinity yInfinity
  targetDegreeCoherence :
    targetDegree (r + l - m) (s + m, t + m) =
      targetDegree l (targetDegree r (s, t))

/-- Transport a permanent representative across the degree equality in the
input package. -/
def transportTarget {O : Operations} {a b : Degree} (h : a = b)
    (z : O.TargetPermanent a) : O.TargetPermanent b := h ▸ z

/-- The open Theorem 6.1 statement over an explicit page and extension
interface. -/
theorem generalized_leibniz :
    ∀ (O : Operations) (I : Input O),
      O.targetDifferential (I.r + I.l - I.m)
          (I.r - 1 - I.m + I.e) (I.s + I.m, I.t + I.m) I.y =
        transportTarget I.targetDegreeCoherence.symm I.yInfinity := by
  sorry

end KIP126.Solution.Tools.Thm6_1Leibniz
