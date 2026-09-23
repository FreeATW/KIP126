import KIPBase.multiplicativeSS.TriangulatedTodaBracket
import KIPBase.multiplicativeSS.AdamsMasseyProduct
import KIPBase.multiplicativeSS.AdamsDetection
import KIPBase.multiplicativeSS.MossCrossing

/-!
# Moss convergence: formal statement for the mapping Adams spectral sequence

`Statement` below is the proposition to be proved, not an axiom or a proof of
Moss convergence. The two non-crossing conditions use the Moss direction
defined in `MossCrossing`, opposite to `SpectralSequence.Crossing`.
-/

namespace KIPBase.StableHomotopy.Moss

open CategoryTheory CategoryTheory.Pretriangulated KIPBase.SpectralSequence

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-- Tower-level data needed in addition to the associated-graded
identification in `Convergence`. The residual injectivity condition is the
weak-convergence condition used in Moss's argument. This structure does not
construct an Adams tower; an actual tower must supply its fields. -/
structure MappingAdamsTower (X Y : FiniteSpectra 𝒮) where
  stage : ℕ → 𝒮
  restrict : ∀ s t : ℕ, s ≤ t → (stage t ⟶ stage s)
  restrict_self : ∀ s, restrict s s le_rfl = 𝟙 (stage s)
  restrict_comp : ∀ s t u (hst : s ≤ t) (htu : t ≤ u),
    restrict t u htu ≫ restrict s t hst =
      restrict s u (hst.trans htu)
  toTarget : ∀ s, stage s ⟶ Y.1
  toTarget_compatible : ∀ s t (hst : s ≤ t),
    restrict s t hst ≫ toTarget s = toTarget t
  filtration_image : ∀ (s : ℕ) (n : ℤ) (f : X.1⟦n⟧ ⟶ Y.1),
    (adamsMappingConvergingSS_abutmentEquiv X.1 Y.1 X.2 Y.2 n).symm
        ((mappingSpectrumHomotopy n X.1 Y.1).symm f) ∈
      Set.range ((AdamsDetection.A X Y).F.F s n).arrow ↔
      ∃ g : X.1⟦n⟧ ⟶ stage s, g ≫ toTarget s = f
  weak_convergence : ∀ (s : ℕ) (n : ℤ)
      (f : X.1⟦n⟧ ⟶ stage (s + 1)),
    (∀ (t : ℕ) (hst : s + 1 ≤ t), ∃ g : X.1⟦n⟧ ⟶ stage t,
      g ≫ restrict (s + 1) t hst = f) →
    f ≫ restrict s (s + 1) (Nat.le_succ s) = 0 → f = 0

/-- The stem of an Adams bidegree `(filtration, total degree)`. -/
def stem (k : ℤ × ℤ) : ℤ := k.2 - k.1

/-- Regard a class in the Adams abutment as a stable map in its stem degree. -/
noncomputable def abutmentMap (X Y : FiniteSpectra 𝒮) (k : ℤ × ℤ)
    (α : (AdamsDetection.A X Y).A
      ((AdamsDetection.A X Y).conv.reindex k).2) : X.1⟦stem k⟧ ⟶ Y.1 := by
  have hk : ((AdamsDetection.A X Y).conv.reindex k).2 = stem k :=
    (adamsMappingConvergingSS_reindex X.1 Y.1 X.2 Y.2 k).2
  rw [← hk]
  exact (mappingSpectrumHomotopy ((AdamsDetection.A X Y).conv.reindex k).2 X.1 Y.1)
    ((adamsMappingConvergingSS_abutmentEquiv X.1 Y.1 X.2 Y.2
      ((AdamsDetection.A X Y).conv.reindex k).2) α)

/-- Shift a graded map by `n`, with the canonical shift-composition isomorphism. -/
noncomputable def shiftMap (X Y : FiniteSpectra 𝒮) (k : ℤ × ℤ) (n : ℤ)
    (α : (AdamsDetection.A X Y).A
      ((AdamsDetection.A X Y).conv.reindex k).2) :
    X.1⟦stem k + n⟧ ⟶ Y.1⟦n⟧ :=
  (shiftFunctorAdd 𝒮 (stem k) n).hom.app X.1 ≫
    (shiftFunctor 𝒮 n).map (abutmentMap X Y k α)

/-- The Massey-product bidegree has stem one above the sum of the input
stems, as required for a shifted Toda bracket. -/
theorem degree_stem (r : ℤ) (i j k : ℤ × ℤ) :
    stem (AdamsPageMasseyProduct.degree r i j k) =
      stem i + (stem j + stem k) + 1 := by
  rcases i with ⟨si, ti⟩
  rcases j with ⟨sj, tj⟩
  rcases k with ⟨sk, tk⟩
  simp only [stem, AdamsPageMasseyProduct.degree, adamsDiffDeg,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

/-- Convert a detected Massey-product class to the morphism with the
suspended source required by the categorical Toda relation. -/
noncomputable def todaMap (r : ℤ) (W Z : FiniteSpectra 𝒮)
    (i j k : ℤ × ℤ)
    (ξ : (AdamsDetection.A W Z).A
      ((AdamsDetection.A W Z).conv.reindex
        (AdamsPageMasseyProduct.degree r i j k)).2) :
    (W.1⟦stem i + (stem j + stem k)⟧)⟦(1 : ℤ)⟧ ⟶ Z.1 := by
  let ξ' : W.1⟦stem i + (stem j + stem k) + 1⟧ ⟶ Z.1 := by
    simpa only [degree_stem] using
      (abutmentMap W Z (AdamsPageMasseyProduct.degree r i j k) ξ)
  exact (shiftFunctorAdd 𝒮 (stem i + (stem j + stem k)) 1).inv.app W.1 ≫ ξ'

/-- The full Moss convergence assertion for mapping Adams spectral sequences.

The input classes are detected by `α`, `β`, `γ`. The products vanish both on
`E_r` and as stable composites. The two mapping spectral sequences in which
those products live must come with compatible, weakly convergent Adams towers.
With no Moss crossing for the product bidegrees, a triple Massey-product class
survives and detects a Toda-bracket element. This definition only *states*
that implication; it does not construct the towers or prove the implication. -/
def Statement : Prop :=
  ∀ (r : ℤ) (hr : 3 ≤ r) (W X Y Z : FiniteSpectra 𝒮)
    (i j k : ℤ × ℤ)
    (_towerWY : MappingAdamsTower W Y)
    (_towerXZ : MappingAdamsTower X Z)
    (a : (AdamsPageMasseyProduct.E W X).Page r i)
    (b : (AdamsPageMasseyProduct.E X Y).Page r j)
    (c : (AdamsPageMasseyProduct.E Y Z).Page r k)
    (α : (AdamsDetection.A W X).A ((AdamsDetection.A W X).conv.reindex i).2)
    (β : (AdamsDetection.A X Y).A ((AdamsDetection.A X Y).conv.reindex j).2)
    (γ : (AdamsDetection.A Y Z).A ((AdamsDetection.A Y Z).conv.reindex k).2),
    let f := shiftMap W X i (stem j + stem k) α
    let g := shiftMap X Y j (stem k) β
    let h := abutmentMap Y Z k γ
    AdamsDetection.DetectsAbutment W X r i a α →
    AdamsDetection.DetectsAbutment X Y r j b β →
    AdamsDetection.DetectsAbutment Y Z r k c γ →
    AdamsPageMasseyProduct.comp W X Y r i j a b = 0 →
    AdamsPageMasseyProduct.comp X Y Z r j k b c = 0 →
    f ≫ g = 0 → g ≫ h = 0 →
    MossCrossing.ForProducts r (W := W) (X := X) (Y := Y) (Z := Z) i j k →
    ∃ (x : (AdamsPageMasseyProduct.E W Z).Page r
        (AdamsPageMasseyProduct.degree r i j k))
      (ξ : (AdamsDetection.A W Z).A
        ((AdamsDetection.A W Z).conv.reindex
          (AdamsPageMasseyProduct.degree r i j k)).2),
      AdamsPageMasseyProduct.Relation r hr x a b c ∧
      AdamsDetection.PermanentCycle W Z r
        (AdamsPageMasseyProduct.degree r i j k) x ∧
      AdamsDetection.DetectsAbutment W Z r
        (AdamsPageMasseyProduct.degree r i j k) x ξ ∧
      TriangulatedTodaBracket.Relation (todaMap r W Z i j k ξ) f g h

/-- The multiplicative (sphere-spectrum) form of Moss convergence. All four
mapping spectra in `Statement` are specialized to the sphere, so the products
are products in the sphere Adams spectral sequence. This is a proposition,
not an additional Moss axiom. -/
def SphereStatement : Prop :=
  let S : FiniteSpectra 𝒮 := ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
  ∀ (r : ℤ) (hr : 3 ≤ r) (i j k : ℤ × ℤ)
    (_towerLeft _towerRight : MappingAdamsTower S S)
    (a : (AdamsPageMasseyProduct.E S S).Page r i)
    (b : (AdamsPageMasseyProduct.E S S).Page r j)
    (c : (AdamsPageMasseyProduct.E S S).Page r k)
    (α : (AdamsDetection.A S S).A ((AdamsDetection.A S S).conv.reindex i).2)
    (β : (AdamsDetection.A S S).A ((AdamsDetection.A S S).conv.reindex j).2)
    (γ : (AdamsDetection.A S S).A ((AdamsDetection.A S S).conv.reindex k).2),
    let f := shiftMap S S i (stem j + stem k) α
    let g := shiftMap S S j (stem k) β
    let h := abutmentMap S S k γ
    AdamsDetection.DetectsAbutment S S r i a α →
    AdamsDetection.DetectsAbutment S S r j b β →
    AdamsDetection.DetectsAbutment S S r k c γ →
    AdamsPageMasseyProduct.comp S S S r i j a b = 0 →
    AdamsPageMasseyProduct.comp S S S r j k b c = 0 →
    f ≫ g = 0 → g ≫ h = 0 →
    MossCrossing.ForProducts r (W := S) (X := S) (Y := S) (Z := S) i j k →
    ∃ (x : (AdamsPageMasseyProduct.E S S).Page r
        (AdamsPageMasseyProduct.degree r i j k))
      (ξ : (AdamsDetection.A S S).A
        ((AdamsDetection.A S S).conv.reindex
          (AdamsPageMasseyProduct.degree r i j k)).2),
      AdamsPageMasseyProduct.Relation r hr x a b c ∧
      AdamsDetection.PermanentCycle S S r
        (AdamsPageMasseyProduct.degree r i j k) x ∧
      AdamsDetection.DetectsAbutment S S r
        (AdamsPageMasseyProduct.degree r i j k) x ξ ∧
      TriangulatedTodaBracket.Relation (todaMap r S S i j k ξ) f g h

/-- Moss convergence, if established for mapping Adams spectral sequences,
implies its multiplicative form for the sphere. -/
theorem sphereStatement_of_statement (hMoss : Statement (𝒮 := 𝒮)) :
    SphereStatement (𝒮 := 𝒮) := by
  dsimp [SphereStatement]
  intro r hr i j k towerLeft towerRight a b c α β γ
  exact hMoss r hr _ _ _ _ i j k towerLeft towerRight a b c α β γ

end KIPBase.StableHomotopy.Moss
