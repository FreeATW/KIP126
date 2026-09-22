import KIP126.Solution.Tools.generalized_leibniz

/-!
# The generalized Mahowald trick (Theorem 6.12)

The statement is parameterized by the normalized triangle and its page
operations.  The arithmetic relations and all four displayed page classes
are fields of the input package, so a later proof cannot hide a missing
triangle or degree transport behind an untyped proposition.
-/
namespace KIP126.Solution.Tools.Thm6_12Mahowald

open KIP126.Solution.Tools.Thm6_1Leibniz

structure Operations where
  MapF : Type
  MapG : Type
  MapH : Type
  XCycle : ℤ → Degree → Type
  YCycle : ℤ → Degree → Type
  ZCycle : ℤ → Degree → Type
  ZPermanent : Degree → Type
  fTarget : ∀ (f : MapF) (page length sourcePage targetPage : ℤ)
    (sourceDegree targetDegree' : Degree),
    XCycle sourcePage sourceDegree → YCycle targetPage targetDegree'
  gExtension : ∀ (g : MapG) (page length sourcePage targetPage : ℤ)
    (sourceDegree targetDegree' : Degree),
    YCycle sourcePage sourceDegree → ZPermanent targetDegree' → Prop
  hExtension : ∀ (h : MapH) (page length sourcePage targetPage : ℤ)
    (sourceDegree targetDegree' : Degree),
    ZCycle sourcePage sourceDegree → XCycle targetPage targetDegree' → Prop
  zDifferential : ∀ (r page : ℤ) (b : Degree),
    ZCycle page b → ZPermanent (targetDegree r b)
  survivesX : ∀ (bound page : ℤ) (b : Degree), XCycle page b → Prop
  moduloBoundary : ∀ (page sourcePage targetPage : ℤ) (b : Degree),
    YCycle sourcePage b → YCycle targetPage b → Prop
  noCrossingH : ∀ (h : MapH) (page : ℤ)
    (sourcePage targetPage : ℤ) (sourceDegree targetDegree' : Degree),
    ZCycle sourcePage sourceDegree → XCycle targetPage targetDegree' → Prop
  noCrossingG : ∀ (g : MapG) (page : ℤ)
    (sourcePage : ℤ) (sourceDegree targetDegree' : Degree),
    YCycle sourcePage sourceDegree → ZPermanent targetDegree' → Prop

structure Input (O : Operations) where
  f : O.MapF
  g : O.MapG
  h : O.MapH
  eF : ℤ
  eG : ℤ
  eH : ℤ
  n : ℤ
  m : ℤ
  l : ℤ
  s : ℤ
  t : ℤ
  r : ℤ
  n1 : ℤ
  m1 : ℤ
  l1 : ℤ
  rPrime : ℤ
  triangleExponents : eF + eG + eH = 1
  r_formula : r = n + m + l
  n1_formula : n1 = n - eF
  m1_formula : m1 = m - eG
  l1_formula : l1 = l - eH
  rPrime_formula : rPrime = r - m1
  bounds : 1 ≤ n1 ∧ 0 ≤ m1 ∧ 0 ≤ l1
  rPrime_coherence : rPrime = n1 + l1 + 1
  x : O.XCycle n1 (s + l, t + l - 1)
  y : O.YCycle (m1 + 1) (s + n + l, t + n + l - 1)
  xBar : O.ZCycle (r - 1) (s, t)
  yBar : O.ZPermanent (targetDegree r (s, t))
  hExtension : O.hExtension h l rPrime (r - 1) n1
    (s, t) (s + l, t + l - 1) xBar x
  zDifferential : O.zDifferential r (r - 1) (s, t) xBar = yBar
  crossingChoice :
    O.noCrossingH h l (r - 1) n1 (s, t) (s + l, t + l - 1) xBar x ∨
      O.noCrossingG g (m1 + 2) (m1 + 1) (s + n + l, t + n + l - 1)
        (targetDegree r (s, t)) y yBar
  gExtension : O.gExtension g m (m1 + 2) (m1 + 1) r
    (s + n + l, t + n + l - 1) (targetDegree r (s, t)) y yBar

/-- The open Theorem 6.12 statement over the explicit triangle package. -/
theorem generalized_mahowald :
    ∀ (O : Operations) (I : Input O),
      O.survivesX (I.n + I.m + I.eH) I.n1
          (I.s + I.l, I.t + I.l - 1) I.x ∧
        O.moduloBoundary I.rPrime (I.m1 + 1) (I.m1 + 1)
          (I.s + I.n + I.l, I.t + I.n + I.l - 1)
          (O.fTarget I.f (I.n + I.m + 1 + I.eH) I.n I.n1
            (I.m1 + 1) (I.s + I.l, I.t + I.l - 1)
            (I.s + I.n + I.l, I.t + I.n + I.l - 1) I.x) I.y := by
  sorry

end KIP126.Solution.Tools.Thm6_12Mahowald
