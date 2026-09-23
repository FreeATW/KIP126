import KIP126.Def.StableHomotopy.Context.Data

/-! Derived facts for the stable-homotopy category interface. -/
namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory Pretriangulated

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

@[simp] theorem sphereSpectrum_eq_unit :
    (SphereSpectrum : C) = 𝟙_ C := rfl

/-- Build the chosen triangle associated with a map when a concrete model
supplies functorial cofiber data. -/
def HoCofiberSequence.ofMorphism {X Y : C} (f : X ⟶ Y)
    [HasFunctorialCofiber (C := C)] : HoCofiberSequence (C := C) where
  X := X
  Y := Y
  Z := HasFunctorialCofiber.cofib f
  f := f
  g := HasFunctorialCofiber.cofibι f
  h := HasFunctorialCofiber.cofibδ f
  distinguished := HasFunctorialCofiber.cofib_distinguished f

private theorem one_plus_neg_one : (1 : ℤ) + (-1) = 0 := by omega

/-! ### Connecting homomorphisms

The connecting map is defined from the shift coherence isomorphisms.  It is
kept in this proof module because a concrete stable model only needs to supply
the distinguished triangle; no additional global axiom is introduced here.
-/

/-- The connecting homomorphism associated to a distinguished cofiber triangle.

For `z : Sⁿ ⟶ Z`, this is the composite
`Sⁿ⁻¹ → Sⁿ⟦-1⟧ → X⟦1⟧⟦-1⟧ → X` applied to `z ≫ h`. -/
noncomputable def connectingHomomorphism (T : HoCofiberSequence (C := C)) (n : ℤ) :
    HomotopyGroup n T.Z →+ HomotopyGroup (n - 1) T.X where
  toFun z :=
    (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
      eqToHom (show (shiftFunctor C n ⋙ shiftFunctor C (-1)).obj SphereSpectrum =
        (shiftFunctor C (-1)).obj ((shiftFunctor C n).obj SphereSpectrum) by
          simp only [Functor.comp_obj]) ≫
      (shiftFunctor C (-1)).map (z ≫ T.h) ≫
        eqToHom (show (shiftFunctor C (-1)).obj ((shiftFunctor C (1 : ℤ)).obj T.X) =
          (shiftFunctor C (1 : ℤ) ⋙ shiftFunctor C (-1)).obj T.X by
            simp only [Functor.comp_obj]) ≫
        (shiftFunctorCompIsoId C 1 (-1) one_plus_neg_one).hom.app T.X ≫
          eqToHom (Functor.id_obj T.X)
  map_zero' := by
    simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  map_add' := by
    intro a b
    rw [Preadditive.add_comp]
    simp only [Functor.map_add]
    rw [Preadditive.add_comp]
    rw [Preadditive.comp_add]
    rw [Preadditive.comp_add]

private theorem shiftFunctor_map_eq_zero {X Y : C} {f : X ⟶ Y} {n : ℤ}
    (h : (shiftFunctor C n).map f = 0) : f = 0 := by
  have inj := (shiftEquiv C n).functor.map_injective (X := X) (Y := Y)
  apply inj
  change (shiftFunctor C n).map f = (shiftFunctor C n).map 0
  rw [h, (shiftFunctor C n).map_zero]

private theorem comp_h_zero_of_connectingHom_zero
    (T : HoCofiberSequence (C := C)) (n : ℤ) (z : HomotopyGroup n T.Z)
    (hz : connectingHomomorphism T n z = 0) : z ≫ T.h = 0 := by
  simp only [connectingHomomorphism, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hz
  let a :=
    (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
      eqToHom (show (shiftFunctor C n ⋙ shiftFunctor C (-1)).obj SphereSpectrum =
        (shiftFunctor C (-1)).obj ((shiftFunctor C n).obj SphereSpectrum) by
          simp only [Functor.comp_obj])
  let m := (shiftFunctor C (-1)).map (z ≫ T.h)
  let b :=
    eqToHom (show (shiftFunctor C (-1)).obj ((shiftFunctor C (1 : ℤ)).obj T.X) =
      (shiftFunctor C (1 : ℤ) ⋙ shiftFunctor C (-1)).obj T.X by
        simp only [Functor.comp_obj]) ≫
      (shiftFunctorCompIsoId C 1 (-1) one_plus_neg_one).hom.app T.X ≫
        eqToHom (Functor.id_obj T.X)
  have hz' : a ≫ m ≫ b = 0 := by
    simpa [a, m, b] using hz
  have hm' : a ≫ m = 0 := by
    apply (cancel_mono b).1
    simpa [Category.assoc] using hz'
  have hm : m = 0 := by
    apply (cancel_epi a).1
    simpa using hm'
  exact shiftFunctor_map_eq_zero hm

/-- The first two maps in a chosen cofiber triangle compose to zero. -/
theorem HoCofiberSequence.fg_zero (T : HoCofiberSequence (C := C)) :
    T.f ≫ T.g = 0 :=
  comp_distTriang_mor_zero₁₂ _ T.distinguished

/-- The last two maps in a chosen cofiber triangle compose to zero. -/
theorem HoCofiberSequence.gh_zero (T : HoCofiberSequence (C := C)) :
    T.g ≫ T.h = 0 :=
  comp_distTriang_mor_zero₂₃ _ T.distinguished

/-- The connecting map composes trivially with the shifted first map. -/
theorem HoCofiberSequence.hf_shift_zero (T : HoCofiberSequence (C := C)) :
    T.h ≫ (shiftFunctor C (1 : ℤ)).map T.f = 0 :=
  comp_distTriang_mor_zero₃₁ _ T.distinguished

/-- The homotopy-group sequence is exact at the third object `Z`. -/
theorem les_homotopy_exact_g (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ∀ (z : HomotopyGroup n T.Z),
      (connectingHomomorphism T n) z = 0 ↔
        ∃ (y : HomotopyGroup n T.Y), (inducedMap T.g n) y = z := by
  intro z
  simp only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · intro hz
    have hz' : z ≫ T.h = 0 := comp_h_zero_of_connectingHom_zero T n z hz
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ _ T.distinguished z hz'
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    simp only [connectingHomomorphism, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Category.assoc, T.gh_zero, Limits.comp_zero, Functor.map_zero,
      Limits.zero_comp]


/-! ### Exactness transferred from the distinguished triangle

The middle-term exactness statement is independent of the connecting
homomorphism construction. It is therefore a direct canonical port of the
corresponding completed KIPBase result. -/

/-- The homotopy-group sequence is exact at the middle object `Y`:
maps into `Y` killed by `g` are exactly those factoring through `f`. -/
theorem les_homotopy_exact_f (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ∀ (y : HomotopyGroup n T.Y),
      (inducedMap T.g n) y = 0 ↔
        ∃ (x : HomotopyGroup n T.X), (inducedMap T.f n) x = y := by
  intro y
  simp only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ _ T.distinguished y hy
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    simp [Category.assoc, T.fg_zero]

/-- Homotopy groups are functorial in the spectrum variable. -/
noncomputable def homotopyGroupFunctor (n : ℤ) :
    C ⥤ AddCommGrpCat.{v} where
  obj := fun X => AddCommGrpCat.mk (HomotopyGroup n X)
  map := fun f => AddCommGrpCat.ofHom (inducedMap f n)
  map_id := by
    intro X
    apply AddCommGrpCat.hom_ext
    ext x
    simp [inducedMap]
  map_comp := by
    intro X Y Z f g
    apply AddCommGrpCat.hom_ext
    ext x
    simp [inducedMap, Category.assoc]

/-- Exactness at the shifted `X` term, transferred through the shift equivalence
from exactness of the distinguished triangle. -/
theorem lesHomotopyExactH :
    ∀ {C : Type u} [StableHomotopyCategory.{u, v} C]
      (T : HoCofiberSequence (C := C)) (n : ℤ),
      ∀ (x : HomotopyGroup (n - 1) T.X),
        (inducedMap T.f (n - 1)) x = 0 ↔
          ∃ z : HomotopyGroup n T.Z, (connectingHomomorphism T n) z = x := by
  intro C _ T n x
  let F := shiftFunctor C (-1 : ℤ)
  let a : (shiftFunctor C (n - 1)).obj SphereSpectrum ≅
      F.obj ((shiftFunctor C n).obj SphereSpectrum) :=
    (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).app SphereSpectrum
  let b := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
  let bX : F.obj ((shiftFunctor C (1 : ℤ)).obj T.X) ≅ T.X := b.app T.X
  let bY : F.obj ((shiftFunctor C (1 : ℤ)).obj T.Y) ≅ T.Y := b.app T.Y
  have hc (z : HomotopyGroup n T.Z) :
      connectingHomomorphism T n z = a.hom ≫ F.map (z ≫ T.h) ≫ bX.hom := by
    change a.hom ≫ 𝟙 _ ≫ F.map (z ≫ T.h) ≫ 𝟙 _ ≫ bX.hom ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  have hb : bX.inv ≫ F.map ((shiftFunctor C (1 : ℤ)).map T.f) =
      T.f ≫ bY.inv := (b.inv.naturality T.f).symm
  constructor
  · intro hx
    change x ≫ T.f = 0 at hx
    let w := F.preimage (a.inv ≫ x ≫ bX.inv)
    have hw : F.map w = a.inv ≫ x ≫ bX.inv := F.map_preimage _
    have hwf : w ≫ (shiftFunctor C (1 : ℤ)).map T.f = 0 := by
      apply F.map_injective
      rw [Functor.map_comp, hw, Functor.map_zero]
      simp only [Category.assoc, hb, ← Category.assoc x T.f, hx,
        Limits.zero_comp, Limits.comp_zero]
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₁ _ T.distinguished w hwf
    change HomotopyGroup n T.Z at z
    change w = z ≫ T.h at hz
    refine ⟨z, ?_⟩
    rw [hc, ← hz, hw]
    simp
  · rintro ⟨z, rfl⟩
    change connectingHomomorphism T n z ≫ T.f = 0
    rw [hc]
    have hb' : bX.hom ≫ T.f =
        F.map ((shiftFunctor C (1 : ℤ)).map T.f) ≫ bY.hom :=
      (b.hom.naturality T.f).symm
    simp only [Category.assoc, hb', ← F.map_comp_assoc,
      T.hf_shift_zero, Limits.comp_zero, F.map_zero, Limits.zero_comp]

end KIP126.StableHomotopy
