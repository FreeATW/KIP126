import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.Def.SpectralSequence.PageLevel.Data
import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Synthetic spectral-sequence basics

This is the concrete three-graded slice used by the first classical--synthetic
comparison.  The spectral-sequence object remains Mathlib's object; this file
only supplies the synthetic index and the weight-preserving degree interface.
-/

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

abbrev Tridegree := ℤ × ℤ × ℤ

def syntheticAdamsShift (r : ℕ) : Tridegree := (r, (r : ℤ) - 1, 0)

def syntheticAdamsTarget (r : ℕ) (i : Tridegree) : Tridegree :=
  i + syntheticAdamsShift r

def syntheticAdamsPageLevel : PageLevelConvention where
  firstPage := 2
  admissibleFrom := 2
  page := fun r => r
  cycleLevel := fun r => r - 1
  quotientExponent := fun r => r - 1
  page_first := by norm_num
  page_succ := by intro r; norm_num
  cycle_succ := by intro r; omega
  quotient_succ := by intro r; omega
  cycleLevel_eq_quotientExponent := by intro r; rfl

def syntheticAdamsShape (r : ℤ) : ComplexShape Tridegree :=
  ComplexShape.up' (r, r - 1, 0)

def lambdaDegree : Tridegree := (0, 0, -1)

def lambdaTarget (i : Tridegree) : Tridegree := i + lambdaDegree

abbrev SyntheticAdamsSpectralSequence :=
  CategoryTheory.SpectralSequence F2ModuleCat syntheticAdamsShape 2

def lambdaPage (E : SyntheticAdamsSpectralSequence) (r : ℤ)
    (hr : 2 ≤ r) : HomologicalComplex F2ModuleCat (syntheticAdamsShape r) where
  X i := (E.page r hr).X (lambdaTarget i)
  d i j := (E.page r hr).d (lambdaTarget i) (lambdaTarget j)
  shape i j hij := by
    apply (E.page r hr).shape _ _
    intro h
    apply hij
    rcases i with ⟨s, t, w⟩
    rcases j with ⟨s', t', w'⟩
    dsimp [syntheticAdamsShape, lambdaTarget, lambdaDegree] at h ⊢
    apply add_right_cancel (b := (0, 0, -1))
    simpa [add_assoc, add_comm, add_left_comm] using h
  d_comp_d' i j k hij hjk := by
    rcases i with ⟨s, t, w⟩
    rcases j with ⟨s', t', w'⟩
    rcases k with ⟨s'', t'', w''⟩
    dsimp [syntheticAdamsShape, lambdaTarget, lambdaDegree] at hij hjk ⊢
    exact (E.page r hr).d_comp_d' _ _ _
      (by
        apply add_right_cancel (b := (0, 0, -1))
        simpa [add_assoc, add_comm, add_left_comm] using hij)
      (by
        apply add_right_cancel (b := (0, 0, -1))
        simpa [add_assoc, add_comm, add_left_comm] using hjk)

structure SyntheticLambdaAction (E : SyntheticAdamsSpectralSequence) where
  map : ∀ (r : ℤ) (hr : 2 ≤ r), E.page r hr ⟶ lambdaPage E r hr
  pagePassage : ∀ (r : ℤ) (hr : 2 ≤ r) (i : Tridegree),
    (lambdaPage E r hr).homology i ≅
      (E.page (r + 1) (by omega)).X (lambdaTarget i)
  page_passage_comm : ∀ (r : ℤ) (hr : 2 ≤ r) (i : Tridegree),
    HomologicalComplex.homologyMap (map r hr) i ≫ (pagePassage r hr i).hom =
      (E.iso r (r + 1) i rfl hr).hom ≫ (map (r + 1) (by omega)).f i

def lambdaMapFromAction {E : SyntheticAdamsSpectralSequence}
    (action : SyntheticLambdaAction E) (i : Tridegree) :
    (E.page 2).X i ⟶ (E.page 2).X (lambdaTarget i) :=
  (action.map 2 (by norm_num)).f i

structure SyntheticAdamsSS where
  sequence : SyntheticAdamsSpectralSequence
  lambdaAction : SyntheticLambdaAction sequence
  h₄ : (sequence.page 2).X (1, 16, 16)
  h₀h₃Squared : (sequence.page 2).X (3, 17, 17)
  weightPreserving : ∀ (r : ℤ) (hr : 2 ≤ r) (i j : Tridegree),
    (syntheticAdamsShape r).Rel i j →
      (sequence.page r).d i j ≠ 0 → i.2.2 = j.2.2

namespace SyntheticAdamsSS

def E₂ (A : SyntheticAdamsSS) := A.sequence.page 2
def E₃ (A : SyntheticAdamsSS) := A.sequence.page 3

def e₂ToE₃ (A : SyntheticAdamsSS) (i : Tridegree) :
    (A.E₂).homology i ≅ (A.E₃).X i :=
  A.sequence.iso 2 3 i rfl (by norm_num)

def d₂ (A : SyntheticAdamsSS) (i : Tridegree) :
    (A.E₂).X i ⟶ (A.E₂).X (syntheticAdamsTarget 2 i) :=
  (A.E₂).d i (syntheticAdamsTarget 2 i)

def lambdaMap (A : SyntheticAdamsSS) (i : Tridegree) :
    A.E₂.X i ⟶ A.E₂.X (lambdaTarget i) :=
  lambdaMapFromAction A.lambdaAction i

theorem lambdaMap_comm (A : SyntheticAdamsSS) (i j : Tridegree) :
    A.lambdaMap i ≫ A.E₂.d (lambdaTarget i) (lambdaTarget j) =
      A.E₂.d i j ≫ A.lambdaMap j := by
  exact (A.lambdaAction.map 2 (by norm_num)).comm i j

end SyntheticAdamsSS

@[simp] theorem syntheticAdamsShift_two :
    syntheticAdamsShift 2 = (2, 1, 0) := by
  norm_num [syntheticAdamsShift]

@[simp] theorem syntheticAdamsTarget_two (i : Tridegree) :
    syntheticAdamsTarget 2 i = (i.1 + 2, i.2.1 + 1, i.2.2) := by
  apply Prod.ext
  · simp [syntheticAdamsTarget, syntheticAdamsShift]
  · apply Prod.ext <;> simp [syntheticAdamsTarget, syntheticAdamsShift]

@[simp] theorem syntheticAdamsShape_rel (r : ℕ) (i : Tridegree) :
    (syntheticAdamsShape r).Rel i (syntheticAdamsTarget r i) := by
  simp [syntheticAdamsShape, syntheticAdamsTarget, syntheticAdamsShift]

def forgetWeight (i : Tridegree) : KIP126.Classical.Adams.Bidegree :=
  (i.1, i.2.1)

def nuDegree (b : KIP126.Classical.Adams.Bidegree) : Tridegree :=
  (b.1, b.2, b.2)

def fixedWeightPage (E : SyntheticAdamsSpectralSequence) (w : ℤ)
    (r : ℤ) (hr : 2 ≤ r) :
    HomologicalComplex F2ModuleCat
      (KIP126.Classical.Adams.classicalAdamsShape r) where
  X b := (E.page r hr).X (b.1, b.2, w)
  d a b := (E.page r hr).d (a.1, a.2, w) (b.1, b.2, w)
  shape a b hab := by
    apply (E.page r hr).shape _ _
    intro h
    apply hab
    rcases a with ⟨s, t⟩
    rcases b with ⟨s', t'⟩
    dsimp [KIP126.Classical.Adams.classicalAdamsShape,
      syntheticAdamsShape] at h ⊢
    exact congrArg (fun x : Tridegree => (x.1, x.2.1)) h
  d_comp_d' a b c hab hbc := by
    exact (E.page r hr).d_comp_d' (a.1, a.2, w) (b.1, b.2, w) (c.1, c.2, w)
      (by
        dsimp [KIP126.Classical.Adams.classicalAdamsShape,
          syntheticAdamsShape] at hab ⊢
        exact by simpa [ComplexShape.up'] using
          (show a.1 + r = b.1 ∧ a.2 + (r - 1) = b.2 by
            exact ⟨congrArg Prod.fst hab, congrArg Prod.snd hab⟩))
      (by
        dsimp [KIP126.Classical.Adams.classicalAdamsShape,
          syntheticAdamsShape] at hbc ⊢
        exact by simpa [ComplexShape.up'] using
          (show b.1 + r = c.1 ∧ b.2 + (r - 1) = c.2 by
            exact ⟨congrArg Prod.fst hbc, congrArg Prod.snd hbc⟩))

@[simp] theorem forgetWeight_nuDegree
    (b : KIP126.Classical.Adams.Bidegree) :
    forgetWeight (nuDegree b) = b := by
  cases b
  rfl

@[simp] theorem lambdaTarget_weight (i : Tridegree) :
    (lambdaTarget i).2.2 = i.2.2 - 1 := by
  rcases i with ⟨s, t, w⟩
  simp [lambdaTarget, lambdaDegree, sub_eq_add_neg]

@[simp] theorem forgetWeight_add_shift (r : ℕ) (i : Tridegree) :
    forgetWeight (syntheticAdamsTarget r i) =
      KIP126.Classical.Adams.classicalAdamsTarget r (forgetWeight i) := by
  apply Prod.ext <;>
    simp [forgetWeight, syntheticAdamsTarget, syntheticAdamsShift,
      KIP126.Classical.Adams.classicalAdamsTarget,
      KIP126.Classical.Adams.classicalAdamsShift]

theorem weightPreserving_differential (A : SyntheticAdamsSS) (r : ℕ)
    (hr : 2 ≤ r)
    (i : Tridegree)
    (h : (A.sequence.page (r : ℤ)).d i (syntheticAdamsTarget r i) ≠ 0) :
    i.2.2 = (syntheticAdamsTarget r i).2.2 := by
  exact A.weightPreserving (r : ℤ) (by omega) i
    (syntheticAdamsTarget r i) (syntheticAdamsShape_rel r i) h

end KIP126.Synthetic.SpectralSequence
