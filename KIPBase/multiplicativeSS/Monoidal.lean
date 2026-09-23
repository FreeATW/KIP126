/-
  KIPBase.multiplicativeSS.Monoidal

  An abstract monoidal product on spectral sequences.  The universal property
  is stated at the level at which multiplicative spectral sequences are used:
  a pairing is exactly a spectral-sequence morphism out of the tensor product.
-/
import KIPBase.multiplicativeSS.Basic

namespace KIPBase.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- A chosen tensor product on spectral sequences with the universal property
for multiplicative pairings.  `pairingEquiv` is the defining datum: it rules
out treating a pagewise product and a map from a separately chosen tensor
spectral sequence as unrelated structures. -/
structure SpectralSequenceMonoidalStructure
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  tensor : SpectralSequence C ι → SpectralSequence C ι → SpectralSequence C ι
  unit : SpectralSequence C ι
  /-- A pairing of `E₁` and `E₂` with target `E₃` is represented uniquely by
  a spectral-sequence morphism from their tensor product. -/
  pairingEquiv : ∀ (E₁ E₂ E₃ : SpectralSequence C ι),
    SSPairing E₁ E₂ E₃ ≃ SpectralSequenceMorphism (tensor E₁ E₂) E₃
  associator : ∀ (E₁ E₂ E₃ : SpectralSequence C ι),
    SpectralSequenceMorphism (tensor (tensor E₁ E₂) E₃)
      (tensor E₁ (tensor E₂ E₃))
  leftUnitor : ∀ (E : SpectralSequence C ι),
    SpectralSequenceMorphism (tensor unit E) E
  rightUnitor : ∀ (E : SpectralSequence C ι),
    SpectralSequenceMorphism (tensor E unit) E

/-- A pairing in the monoidal category of spectral sequences is, by
definition, a morphism out of the tensor product.  This definition is
separate from the older pagewise `SSPairing`: `pairingEquiv` above is precisely
the additional theorem/data identifying that concrete presentation with the
monoidal one. -/
abbrev MonoidalSSPairing
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (M : SpectralSequenceMonoidalStructure (C := C) ι)
    (E₁ E₂ E₃ : SpectralSequence C ι) : Type _ :=
  SpectralSequenceMorphism (M.tensor E₁ E₂) E₃

/-- **Core tensor--pairing equivalence.**  It is proved by reflexivity because
`MonoidalSSPairing` is defined to be the representing morphism type. -/
def monoidalPairingEquivTensorMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (M : SpectralSequenceMonoidalStructure (C := C) ι)
    (E₁ E₂ E₃ : SpectralSequence C ι) :
    MonoidalSSPairing M E₁ E₂ E₃ ≃
      SpectralSequenceMorphism (M.tensor E₁ E₂) E₃ :=
  Equiv.refl _

@[simp]
theorem monoidalPairingEquivTensorMorphism_apply
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (M : SpectralSequenceMonoidalStructure (C := C) ι)
    (E₁ E₂ E₃ : SpectralSequence C ι)
    (f : MonoidalSSPairing M E₁ E₂ E₃) :
    monoidalPairingEquivTensorMorphism M E₁ E₂ E₃ f = f :=
  rfl

/-- Convert a pairing into its representing tensor morphism. -/
def SpectralSequenceMonoidalStructure.toTensorMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (M : SpectralSequenceMonoidalStructure (C := C) ι)
    {E₁ E₂ E₃ : SpectralSequence C ι} (P : SSPairing E₁ E₂ E₃) :
    SpectralSequenceMorphism (M.tensor E₁ E₂) E₃ :=
  (M.pairingEquiv E₁ E₂ E₃) P

/-- Recover the pairing represented by a tensor morphism. -/
def SpectralSequenceMonoidalStructure.ofTensorMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (M : SpectralSequenceMonoidalStructure (C := C) ι)
    {E₁ E₂ E₃ : SpectralSequence C ι}
    (f : SpectralSequenceMorphism (M.tensor E₁ E₂) E₃) : SSPairing E₁ E₂ E₃ :=
  (M.pairingEquiv E₁ E₂ E₃).symm f

@[simp]
theorem SpectralSequenceMonoidalStructure.of_toTensorMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (M : SpectralSequenceMonoidalStructure (C := C) ι)
    {E₁ E₂ E₃ : SpectralSequence C ι} (P : SSPairing E₁ E₂ E₃) :
    M.ofTensorMorphism (M.toTensorMorphism P) = P :=
  (M.pairingEquiv E₁ E₂ E₃).left_inv P

@[simp]
theorem SpectralSequenceMonoidalStructure.to_ofTensorMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (M : SpectralSequenceMonoidalStructure (C := C) ι)
    {E₁ E₂ E₃ : SpectralSequence C ι}
    (f : SpectralSequenceMorphism (M.tensor E₁ E₂) E₃) :
    M.toTensorMorphism (M.ofTensorMorphism f) = f :=
  (M.pairingEquiv E₁ E₂ E₃).right_inv f

end KIPBase.SpectralSequence
