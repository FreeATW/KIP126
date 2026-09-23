import KIP126.Def.SpectralSequence.Basic.Proofs

/-!
# Categories of nested-subobject spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The category of graded `SSData` families and their underlying morphisms. -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Category.{max w v} (GradedSSData C ι) where
  Hom D D' := UnderlyingMorphism ι D.data D'.data
  id _ := ⟨fun _ => 𝟙 _⟩
  comp f g := ⟨fun k => f.φ k ≫ g.φ k⟩
  id_comp f := UnderlyingMorphism.ext (funext fun k => Category.id_comp (f.φ k))
  comp_id f := UnderlyingMorphism.ext (funext fun k => Category.comp_id (f.φ k))
  assoc f g h :=
    UnderlyingMorphism.ext (funext fun k => Category.assoc (f.φ k) (g.φ k) (h.φ k))

/-- The category of pre-spectral sequences. -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Category.{max w v} (PreSS C ι) where
  Hom E E' := PreSSMorphism E E'
  id E := {
    φ := fun _ => 𝟙 _
    preserves_Z := fun _ _ => ⟨𝟙 _, by simp⟩
    preserves_B := fun _ _ => ⟨𝟙 _, by simp⟩
    comm_d := fun _ _ => ⟨𝟙 _, 𝟙 _, by simp⟩ }
  comp f g := {
    φ := fun k => f.φ k ≫ g.φ k
    preserves_Z := fun k r =>
      ⟨(f.preserves_Z k r).choose ≫ (g.preserves_Z k r).choose, by
        rw [Category.assoc, (g.preserves_Z k r).choose_spec,
          ← Category.assoc, (f.preserves_Z k r).choose_spec, Category.assoc]⟩
    preserves_B := fun k r =>
      ⟨(f.preserves_B k r).choose ≫ (g.preserves_B k r).choose, by
        rw [Category.assoc, (g.preserves_B k r).choose_spec,
          ← Category.assoc, (f.preserves_B k r).choose_spec, Category.assoc]⟩
    comm_d := fun r k =>
      ⟨(f.comm_d r k).choose ≫ (g.comm_d r k).choose,
       (f.comm_d r k).choose_spec.choose ≫ (g.comm_d r k).choose_spec.choose, by
        rcases (f.comm_d r k).choose_spec.choose_spec with h₁
        rcases (g.comm_d r k).choose_spec.choose_spec with h₂
        calc
          ((f.comm_d r k).choose ≫ (g.comm_d r k).choose) ≫ _ =
              (f.comm_d r k).choose ≫ ((g.comm_d r k).choose ≫ _) :=
            Category.assoc _ _ _
          _ = (f.comm_d r k).choose ≫
              (_ ≫ (g.comm_d r k).choose_spec.choose) := by
                conv_lhs => rw [h₂]
          _ = ((f.comm_d r k).choose ≫ _) ≫
              (g.comm_d r k).choose_spec.choose := (Category.assoc _ _ _).symm
          _ = (_ ≫ (f.comm_d r k).choose_spec.choose) ≫
              (g.comm_d r k).choose_spec.choose := by
                conv_lhs => rw [h₁]
          _ = _ ≫ ((f.comm_d r k).choose_spec.choose ≫
              (g.comm_d r k).choose_spec.choose) := Category.assoc _ _ _⟩ }
  id_comp f := PreSSMorphism.ext (funext fun k => Category.id_comp (f.φ k))
  comp_id f := PreSSMorphism.ext (funext fun k => Category.comp_id (f.φ k))
  assoc f g h :=
    PreSSMorphism.ext (funext fun k => Category.assoc (f.φ k) (g.φ k) (h.φ k))

/-- Forget a pre-spectral sequence to its graded family of nested-subobject data. -/
def PreSS.forget {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    PreSS C ι ⥤ GradedSSData C ι where
  obj E := ⟨E.ssData⟩
  map f := ⟨f.φ⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The forgetful functor from `PreSS` is faithful. -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Functor.Faithful (PreSS.forget (C := C) (ι := ι)) where
  map_injective h := PreSSMorphism.ext (congrArg UnderlyingMorphism.φ h)

/-- The category of nested-subobject spectral sequences. -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Category.{max w v} (SpectralSequence C ι) where
  Hom E E' := SpectralSequenceMorphism E E'
  id E := {
    φ := fun _ => 𝟙 _
    preserves_Z := fun _ _ => ⟨𝟙 _, by simp⟩
    preserves_B := fun _ _ => ⟨𝟙 _, by simp⟩
    comm_d := fun _ _ => ⟨𝟙 _, 𝟙 _, by simp⟩ }
  comp f g := {
    φ := fun k => f.φ k ≫ g.φ k
    preserves_Z := fun k r =>
      ⟨(f.preserves_Z k r).choose ≫ (g.preserves_Z k r).choose, by
        rw [Category.assoc, (g.preserves_Z k r).choose_spec,
          ← Category.assoc, (f.preserves_Z k r).choose_spec, Category.assoc]⟩
    preserves_B := fun k r =>
      ⟨(f.preserves_B k r).choose ≫ (g.preserves_B k r).choose, by
        rw [Category.assoc, (g.preserves_B k r).choose_spec,
          ← Category.assoc, (f.preserves_B k r).choose_spec, Category.assoc]⟩
    comm_d := fun r k =>
      ⟨(f.comm_d r k).choose ≫ (g.comm_d r k).choose,
       (f.comm_d r k).choose_spec.choose ≫ (g.comm_d r k).choose_spec.choose, by
        rcases (f.comm_d r k).choose_spec.choose_spec with h₁
        rcases (g.comm_d r k).choose_spec.choose_spec with h₂
        calc
          ((f.comm_d r k).choose ≫ (g.comm_d r k).choose) ≫ _ =
              (f.comm_d r k).choose ≫ ((g.comm_d r k).choose ≫ _) :=
            Category.assoc _ _ _
          _ = (f.comm_d r k).choose ≫
              (_ ≫ (g.comm_d r k).choose_spec.choose) := by
                conv_lhs => rw [h₂]
          _ = ((f.comm_d r k).choose ≫ _) ≫
              (g.comm_d r k).choose_spec.choose := (Category.assoc _ _ _).symm
          _ = (_ ≫ (f.comm_d r k).choose_spec.choose) ≫
              (g.comm_d r k).choose_spec.choose := by
                conv_lhs => rw [h₁]
          _ = _ ≫ ((f.comm_d r k).choose_spec.choose ≫
              (g.comm_d r k).choose_spec.choose) := Category.assoc _ _ _⟩ }
  id_comp f := SpectralSequenceMorphism.ext
    (funext fun k => Category.id_comp (f.φ k))
  comp_id f := SpectralSequenceMorphism.ext
    (funext fun k => Category.comp_id (f.φ k))
  assoc f g h := SpectralSequenceMorphism.ext
    (funext fun k => Category.assoc (f.φ k) (g.φ k) (h.φ k))

/-- Spectral-sequence morphisms are exactly morphisms of the underlying `PreSS`. -/
def SpectralSequenceMorphism.equivPreSSMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : SpectralSequence C ι) :
    SpectralSequenceMorphism E E' ≃ PreSSMorphism E.toPreSS E'.toPreSS where
  toFun f := {
    φ := f.φ
    preserves_Z := f.preserves_Z
    preserves_B := f.preserves_B
    comm_d := f.comm_d }
  invFun g := {
    φ := g.φ
    preserves_Z := g.preserves_Z
    preserves_B := g.preserves_B
    comm_d := g.comm_d }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Inclusion of spectral sequences into pre-spectral sequences. -/
def SpectralSequence.inclusion
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    SpectralSequence C ι ⥤ PreSS C ι where
  obj E := E.toPreSS
  map f := SpectralSequenceMorphism.equivPreSSMorphism _ _ f
  map_id _ := PreSSMorphism.ext rfl
  map_comp _ _ := PreSSMorphism.ext rfl

/-- The inclusion of spectral sequences is faithful. -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Functor.Faithful (SpectralSequence.inclusion (C := C) (ι := ι)) where
  map_injective h := SpectralSequenceMorphism.ext (congrArg (fun m => m.φ) h)

/-- The inclusion of spectral sequences is full. -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Functor.Full (SpectralSequence.inclusion (C := C) (ι := ι)) where
  map_surjective g :=
    ⟨(SpectralSequenceMorphism.equivPreSSMorphism _ _).symm g,
      (SpectralSequenceMorphism.equivPreSSMorphism _ _).apply_symm_apply g⟩

/-- The inclusion of spectral sequences is fully faithful. -/
noncomputable def SpectralSequence.inclusionFullyFaithful
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    (SpectralSequence.inclusion (C := C) (ι := ι)).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end KIP126.Core.SpectralSequence
