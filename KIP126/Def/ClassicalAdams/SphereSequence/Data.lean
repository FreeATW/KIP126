import KIP126.Def.ClassicalAdams.Convergence.StrongData

/-! Sphere Adams classes, products, and the h₄ differential statement. -/
namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

namespace ClassicalAdamsSS

variable {stable : StableHomotopyContext} {X : stable.Spectrum}

/-- The first two displayed pages of a chosen Adams sequence. -/
def E₂ (A : ClassicalAdamsSS stable X) := A.sequence.page 2
def E₃ (A : ClassicalAdamsSS stable X) := A.sequence.page 3

/-- Mathlib's page-passage isomorphism for the `E₂ → E₃` slice. -/
def e₂ToE₃ (A : ClassicalAdamsSS stable X) (b : Bidegree) :
    (A.E₂).homology b ≅ (A.E₃).X b :=
  A.sequence.iso 2 3 b rfl (by norm_num)

/-- The actual page-2 differential component at the Adams target degree. -/
def d₂ (A : ClassicalAdamsSS stable X) (b : Bidegree) :
    (A.E₂).X b ⟶ (A.E₂).X (classicalAdamsTarget 2 b) :=
  (A.E₂).d b (classicalAdamsTarget 2 b)

theorem d₂_shape (_A : ClassicalAdamsSS stable X) (b : Bidegree) :
    (classicalAdamsShape 2).Rel b (classicalAdamsTarget 2 b) :=
  classicalAdamsShape_two_rel b

end ClassicalAdamsSS

/-- A named page-2 class, retaining its representative in the Mathlib page. -/
structure AdamsClass {stable : StableHomotopyContext} {X : stable.Spectrum}
    (A : ClassicalAdamsSS stable X) where
  name : String
  degree : Bidegree
  representative : (A.E₂).X degree

def transportRepresentative {stable : StableHomotopyContext}
    {X : stable.Spectrum} {A : ClassicalAdamsSS stable X}
    (x : AdamsClass A) {degree : Bidegree} (h : x.degree = degree) :
    (A.E₂).X degree :=
  (eqToHom (congrArg (fun b => (A.E₂).X b) h)).hom x.representative

/-- Transport a page element along an equality of Adams bidegrees. -/
def transportPageElement {stable : StableHomotopyContext}
    {X : stable.Spectrum} (A : ClassicalAdamsSS stable X)
    {source target : Bidegree} (h : source = target)
    (x : (A.E₂).X source) : (A.E₂).X target :=
  (eqToHom (congrArg (fun b => (A.E₂).X b) h)).hom x

/-! ### Sphere multiplication versus general external pairings -/

/-- Explicit internal product data for the sphere Adams page only. -/
structure SphereAdamsMultiplication {stable : StableHomotopyContext}
    (A : ClassicalAdamsSS stable stable.sphere) where
  product : AdamsClass A → AdamsClass A → AdamsClass A
  product_degree : ∀ x y, (product x y).degree = x.degree + y.degree

/-- The standard named sphere classes, supplied together with their page
representatives by the caller. -/
structure SphereAdamsPresentation {stable : StableHomotopyContext}
    (A : ClassicalAdamsSS stable stable.sphere) where
  h : ℕ → AdamsClass A
  h_degree : ∀ j, (h j).degree = (1, (2 : ℤ) ^ j)
  multiplication : SphereAdamsMultiplication A

def sphereProduct {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) (x y : AdamsClass A) : AdamsClass A :=
  P.multiplication.product x y

/-- The named page-2 class represented by the square `h₆²` in the sphere
Adams presentation.  This is defined from the existing Adams object and its
chosen sphere multiplication; it is not a second, independent carrier. -/
def h6Square {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) : AdamsClass A :=
  sphereProduct P (P.h 6) (P.h 6)

theorem h6Square_degree {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) :
    (h6Square P).degree = (2, (128 : ℤ)) := by
  rw [h6Square, sphereProduct, P.multiplication.product_degree,
    P.h_degree]
  norm_num

/-- Algebraic laws for a chosen sphere presentation.  The product on named
classes is required to be represented by a bilinear, unital, associative
product on the actual Mathlib `E₂` page and to satisfy the page-`2` Leibniz
rule.  The named generators and the `h₀h₃²` target are explicitly nonzero. -/
structure SphereAdamsAlgebraPresentation {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) where
  productMap : ∀ a b : Bidegree,
    (A.E₂).X a →ₗ[F2] (A.E₂).X b →ₗ[F2] (A.E₂).X (a + b)
  product_representation : ∀ x y,
    transportRepresentative (sphereProduct P x y)
        (P.multiplication.product_degree x y) =
      productMap x.degree y.degree x.representative y.representative
  unit : (A.E₂).X (0, 0)
  unit_left : ∀ (b : Bidegree) (x : (A.E₂).X b),
    transportPageElement A (by simp : (0, 0) + b = b)
        (productMap (0, 0) b unit x) = x
  unit_right : ∀ (a : Bidegree) (x : (A.E₂).X a),
    transportPageElement A (by simp : a + (0, 0) = a)
        (productMap a (0, 0) x unit) = x
  product_assoc : ∀ (a b c : Bidegree) (x : (A.E₂).X a)
      (y : (A.E₂).X b) (z : (A.E₂).X c),
    transportPageElement A (add_assoc a b c)
        (productMap (a + b) c (productMap a b x y) z) =
      productMap a (b + c) x (productMap b c y z)
  d₂_leibniz : ∀ (a b : Bidegree) (x : (A.E₂).X a) (y : (A.E₂).X b),
    (A.d₂ (a + b)).hom (productMap a b x y) =
      transportPageElement A
          (by
            apply Prod.ext <;>
              simp [classicalAdamsTarget, classicalAdamsShift, add_assoc,
                add_comm, add_left_comm] :
            classicalAdamsTarget 2 a + b = classicalAdamsTarget 2 (a + b))
          (productMap (classicalAdamsTarget 2 a) b ((A.d₂ a).hom x) y) +
        transportPageElement A
          (by
            apply Prod.ext <;>
              simp [classicalAdamsTarget, classicalAdamsShift, add_assoc] :
            a + classicalAdamsTarget 2 b = classicalAdamsTarget 2 (a + b))
          (productMap a (classicalAdamsTarget 2 b) x ((A.d₂ b).hom y))
  h_nonzero : ∀ j, (P.h j).representative ≠ 0
  h₀h₃Squared_nonzero :
    (sphereProduct P (P.h 0) (sphereProduct P (P.h 3) (P.h 3))).representative ≠ 0

/-- An external page pairing for arbitrary spectra.  Its target is the chosen
smash spectrum, not either input, so it does not assert an internal product. -/
structure ExternalAdamsPairing {stable : StableHomotopyContext}
    {X Y : stable.Spectrum} (AX : ClassicalAdamsSS stable X)
    (AY : ClassicalAdamsSS stable Y)
    (AZ : ClassicalAdamsSS stable (stable.smash X Y)) where
  pair : AdamsClass AX → AdamsClass AY → AdamsClass AZ
  pair_degree : ∀ x y, (pair x y).degree = x.degree + y.degree

/-- Bilinearity and Leibniz compatibility for an external Adams pairing. -/
structure ExternalAdamsPairingLaws {stable : StableHomotopyContext}
    {X Y : stable.Spectrum} {AX : ClassicalAdamsSS stable X}
    {AY : ClassicalAdamsSS stable Y}
    {AZ : ClassicalAdamsSS stable (stable.smash X Y)}
    (pairing : ExternalAdamsPairing AX AY AZ) where
  pairMap : ∀ a b : Bidegree,
    (AX.E₂).X a →ₗ[F2] (AY.E₂).X b →ₗ[F2] (AZ.E₂).X (a + b)
  pair_representation : ∀ x y,
    transportRepresentative (pairing.pair x y) (pairing.pair_degree x y) =
      pairMap x.degree y.degree x.representative y.representative
  d₂_leibniz : ∀ (a b : Bidegree) (x : (AX.E₂).X a) (y : (AY.E₂).X b),
    (AZ.d₂ (a + b)).hom (pairMap a b x y) =
      transportPageElement AZ
          (by
            apply Prod.ext <;>
              simp [classicalAdamsTarget, classicalAdamsShift, add_assoc,
                add_comm, add_left_comm] :
            classicalAdamsTarget 2 a + b = classicalAdamsTarget 2 (a + b))
          (pairMap (classicalAdamsTarget 2 a) b ((AX.d₂ a).hom x) y) +
        transportPageElement AZ
          (by
            apply Prod.ext <;>
              simp [classicalAdamsTarget, classicalAdamsShift, add_assoc] :
            a + classicalAdamsTarget 2 b = classicalAdamsTarget 2 (a + b))
          (pairMap a (classicalAdamsTarget 2 b) x ((AY.d₂ b).hom y))

/-- The sphere page acts on the page of an arbitrary spectrum.  This is kept
separate from `SphereAdamsMultiplication`, so a general Adams sequence gains no
internal multiplication by mere parametrisation. -/
structure SphereAdamsModule {stable : StableHomotopyContext}
    {X : stable.Spectrum} (sphere : ClassicalAdamsSS stable stable.sphere)
    (target : ClassicalAdamsSS stable X) where
  action : AdamsClass sphere → AdamsClass target → AdamsClass target
  action_degree : ∀ x y, (action x y).degree = x.degree + y.degree

/-- A lawful module action of the sphere Adams algebra on a target Adams
page.  Its action is bilinear on representatives, unital, and associative
with the sphere product. -/
structure SphereAdamsModuleLaws {stable : StableHomotopyContext}
    {X : stable.Spectrum} {sphere : ClassicalAdamsSS stable stable.sphere}
    {target : ClassicalAdamsSS stable X}
    {P : SphereAdamsPresentation sphere}
    (algebra : SphereAdamsAlgebraPresentation P)
    (module : SphereAdamsModule sphere target) where
  actionMap : ∀ a b : Bidegree,
    (sphere.E₂).X a →ₗ[F2] (target.E₂).X b →ₗ[F2]
      (target.E₂).X (a + b)
  action_representation : ∀ x y,
    transportRepresentative (module.action x y) (module.action_degree x y) =
      actionMap x.degree y.degree x.representative y.representative
  unit_action : ∀ (b : Bidegree) (x : (target.E₂).X b),
    transportPageElement target (by simp : (0, 0) + b = b)
        (actionMap (0, 0) b algebra.unit x) = x
  action_assoc : ∀ (a b c : Bidegree) (x : (sphere.E₂).X a)
      (y : (sphere.E₂).X b) (z : (target.E₂).X c),
    transportPageElement target (add_assoc a b c)
        (actionMap (a + b) c (algebra.productMap a b x y) z) =
      actionMap a (b + c) x (actionMap b c y z)

/-- The sphere's internal multiplication is the external sphere pairing after
an explicit identification of the smash-square page with the sphere page. -/
structure SphereAdamsExternalCompatibility {stable : StableHomotopyContext}
    {sphere : ClassicalAdamsSS stable stable.sphere}
    {smashSphere : ClassicalAdamsSS stable
      (stable.smash stable.sphere stable.sphere)}
    {P : SphereAdamsPresentation sphere}
    (algebra : SphereAdamsAlgebraPresentation P)
    (pairing : ExternalAdamsPairing sphere sphere smashSphere)
    (pairingLaws : ExternalAdamsPairingLaws pairing) where
  smashToSphere : ∀ b : Bidegree,
    (smashSphere.E₂).X b ≅ (sphere.E₂).X b
  product_eq_external : ∀ (a b : Bidegree) (x : (sphere.E₂).X a)
      (y : (sphere.E₂).X b),
    algebra.productMap a b x y =
      (smashToSphere (a + b)).hom (pairingLaws.pairMap a b x y)

end KIP126.Classical.Adams
