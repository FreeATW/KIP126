import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.Def.Algebra.Coefficients.Data
import KIP126.Def.Synthetic.AdamsSequence.Data
import KIP126.Def.StableHomotopy.Context.Data
import Mathlib.Algebra.Field.ZMod

/-!
# Stable and synthetic data used by the Kervaire endpoint

These structures are interfaces.  They carry the maps, graded groups, and
coherence data that an endpoint proof must consume; they do not assert any
external computation or permanence result.
-/

namespace KIP126.Kervaire

open KIP126.Classical.Adams
open KIP126.Core.Algebra
open KIP126.Synthetic.SpectralSequence

/-- Graded stable homotopy groups attached to a stable context. -/
structure StableHomotopyData (C : StableHomotopyContext) where
  homotopy : ℤ → C.Spectrum → Type
  homotopyAddCommGroup : ∀ (n : ℤ) (X : C.Spectrum), AddCommGroup (homotopy n X)

attribute [instance] StableHomotopyData.homotopyAddCommGroup

/-- A stable map interface with its induced maps on all homotopy groups. -/
structure StableMapData {C : StableHomotopyContext} (H : StableHomotopyData C)
    (X Y : C.Spectrum) where
  map : Type
  induced : ∀ (n : ℤ), H.homotopy n X → H.homotopy n Y

/-- A synthetic stable context with the deformation element and its quotients. -/
structure SyntheticHomotopyContext (C : StableHomotopyContext) where
  Spectrum : Type
  sphere : Spectrum
  homotopy : ℤ × ℤ → Spectrum → Type
  homotopyAddCommGroup : ∀ (d : ℤ × ℤ) (X : Spectrum),
    AddCommGroup (homotopy d X)
  lambda : homotopy (0, -1) sphere
  lambdaPower : ∀ n : ℕ, homotopy (0, -n) sphere
  quotient : ℕ → Spectrum → Spectrum
  quotientMap : ∀ (_n : ℕ) (_X : Spectrum), Spectrum → Spectrum
  unit : Spectrum
  unitIso : unit = sphere

attribute [instance] SyntheticHomotopyContext.homotopyAddCommGroup

/-- A detected synthetic class, retaining both its page representative and
its abutment value. -/
structure SyntheticDetectedClass
    {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    (A : SyntheticAdamsSS) where
  degree : Tridegree
  representative : (A.E₂).X degree
  abutment : S.homotopy (degree.1, degree.2.2) S.sphere

/-- The chosen $θ_5$ and $η$ data used by the near-126 conditions. -/
structure SyntheticTheta5EtaData
    {C : StableHomotopyContext} (S : SyntheticHomotopyContext C)
    (A : SyntheticAdamsSS) where
  theta5 : S.homotopy (62, 64) S.sphere
  theta5Detected : SyntheticDetectedClass (S := S) A
  theta5Degree : theta5Detected.degree = (5, 32, 32)
  eta : S.homotopy (1, 2) S.sphere
  etaDetected : SyntheticDetectedClass (S := S) A
  etaDegree : etaDetected.degree = (1, 2, 2)
  quotientImage : ∀ (n : ℕ), S.homotopy (62, 64) S.sphere →
    S.homotopy (62, 64) (S.quotient n S.sphere)

/-- Page and abutment operations needed to state the three near-126
conditions.  Every operation is supplied with its typing data. -/
structure Near126Input
    {C : StableHomotopyContext} (S : SyntheticHomotopyContext C)
    (A : SyntheticAdamsSS) where
  x12684 : (A.E₂).X (8, 16, 4)
  x1268 : (A.E₂).X (8, 16, 4)
  d6 : (A.E₂).X (8, 16, 4) →ₗ[F2] (A.E₂).X (14, 21, 4)
  x1248 : (A.E₂).X (8, 16, 8)
  x10912 : (A.E₂).X (12, 24, 12)
  h0SquaredX1248 : S.homotopy (124, 128) S.sphere
  h1h4X10912 : S.homotopy (125, 133) S.sphere
  etaAction : S.homotopy (124, 128) S.sphere → S.homotopy (125, 133) S.sphere
  lambda6 : S.homotopy (124, 128) S.sphere → S.homotopy (124, 128) S.sphere
  lambda3 : S.homotopy (125, 133) S.sphere → S.homotopy (125, 133) S.sphere
  lambda6H1h4 : S.homotopy (125, 133) S.sphere → S.homotopy (125, 133) S.sphere
  theta5Square : S.homotopy (124, 128) S.sphere

/-- The exact propositional forms of $C_3$, $C_4$, and $C_5$. -/
structure Near126Conditions
    {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} (D : Near126Input S A) where
  C3 : D.d6 (D.x12684 + D.x1268) = 0
  C4 : D.theta5Square = D.lambda6 D.h0SquaredX1248 ∧
    D.theta5Square ≠ 0
  C5 : D.lambda3 (D.etaAction D.h0SquaredX1248) =
    D.lambda6H1h4 D.h1h4X10912

/-- A framed manifold in dimension `n`, retaining its geometric carrier. -/
structure FramedKervaireContext
    {C : StableHomotopyContext} (H : StableHomotopyData C) where
  Manifold : ℕ → Type
  closedSmoothFramed : ∀ {n : ℕ}, Manifold n → Prop
  framedCobordant : ∀ {n : ℕ}, Manifold n → Manifold n → Prop
  pontryaginThom : ∀ {n : ℕ}, Manifold n → H.homotopy n C.sphere
  middleSpace : ∀ {n : ℕ}, Manifold n → Type
  intersectionPairing : ∀ {n : ℕ} (M : Manifold n),
    middleSpace M → middleSpace M → ZMod 2
  quadraticRefinement : ∀ {n : ℕ} (M : Manifold n),
    middleSpace M → ZMod 2
  arfInvariant : ∀ {n : ℕ}, Manifold n → ZMod 2
  hasKervaireInvariantOne : ∀ {n : ℕ}, Manifold n → Prop
  pontryaginThom_cobordism : ∀ {n : ℕ} {M N : Manifold n},
    framedCobordant M N → pontryaginThom M = pontryaginThom N
  kervaireInvariantOne_iff_arf : ∀ {n : ℕ} (M : Manifold n),
    hasKervaireInvariantOne M ↔ arfInvariant M = 1

/-- Explicit object and grading transports between classical and synthetic
sphere Adams data. -/
structure SphereAdamsCoherence
    {C : StableHomotopyContext} (S : SyntheticHomotopyContext C)
    {A : ClassicalAdamsSS C C.sphere} (B : SyntheticAdamsSS) where
  classicalSphere : C.sphere = C.sphere
  syntheticSphere : S.sphere = S.sphere
  unitName : String
  h5Degree : KIP126.Classical.Adams.Bidegree
  h5Degree_eq : h5Degree = (1, 32)
  regrading : ∀ b : KIP126.Classical.Adams.Bidegree,
    nuDegree b = (b.1, b.2, b.2)

end KIP126.Kervaire
