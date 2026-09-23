import KIP126.Def.SpectralSequence.Convergence.SSData.Proofs

/-!
# Category of convergent nested-subobject spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The category whose objects are convergent nested-subobject spectral sequences. -/
noncomputable instance
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω] {ω' : Type w} :
    Category.{max w v} (ConvergingSS C ω ω') where
  Hom X Y := ConvergenceMorphism X.conv Y.conv
  id X := ⟨
    { eMap := fun _ => 𝟙 _
      aMap := fun _ => 𝟙 _
      filtration_compat := X.F.fcId },
    rfl,
    fun k => by
      simp only [Category.id_comp, Filtration.transportGraded_self,
        Category.comp_id,
        X.F.inducedAssocGradedMap_id (X.conv.reindex k).1 (X.conv.reindex k).2]⟩
  comp {X Y Z} f g := ⟨
    { eMap := fun k => f.eMap k ≫ g.eMap k
      aMap := fun k' => f.aMap k' ≫ g.aMap k'
      filtration_compat := ConvergenceMorphismData.fcComp f g },
    f.reindex_eq.trans g.reindex_eq,
    fun k => by
      show (f.eMap k ≫ g.eMap k) ≫ (Z.conv.iso k).hom ≫
          Z.F.transportGraded
            ((congrFun (f.reindex_eq.trans g.reindex_eq) k).symm) =
        (X.conv.iso k).hom ≫
          Filtration.inducedAssocGradedMap (fun k' => f.aMap k' ≫ g.aMap k')
            (ConvergenceMorphismData.fcComp f g)
            (X.conv.reindex k).1 (X.conv.reindex k).2
      exact ConvergenceMorphism.iso_compat_comp f g k⟩
  id_comp f := ConvergenceMorphism.ext
    (funext fun _ => Category.id_comp _) (funext fun _ => Category.id_comp _)
  comp_id f := ConvergenceMorphism.ext
    (funext fun _ => Category.comp_id _) (funext fun _ => Category.comp_id _)
  assoc f g h := ConvergenceMorphism.ext
    (funext fun _ => Category.assoc _ _ _) (funext fun _ => Category.assoc _ _ _)

end KIP126.Core.SpectralSequence
