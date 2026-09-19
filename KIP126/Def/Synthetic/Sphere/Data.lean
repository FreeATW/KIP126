import KIP126.Def.Synthetic.Context.Data

/-!
# Synthetic spheres and bigraded homotopy groups

These definitions use the explicit suspension and monoidal structures supplied
by `SyntheticCategory`.  Fully-faithful suspension is a witness field of that
class, so the invariance equivalence below is an internal construction rather
than an unproved global theorem.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory MonoidalCategory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The synthetic sphere `S^(0,0)`, the monoidal unit. -/
noncomputable def S00 : Syn := 𝟙_ Syn

/-- The bigraded synthetic sphere `S^(m,n)`. -/
noncomputable def Smn (m n : ℤ) : Syn :=
  (SyntheticCategory.biShift (m, n)).obj S00

/-- The bigraded homotopy class type `[S^(m,n), X]`. -/
abbrev BiHom (m n : ℤ) (X : Syn) : Type v := Smn m n ⟶ X

/-- The additive-group structure on a bigraded homotopy group. -/
@[reducible] noncomputable def biHomotopyGroup (m n : ℤ) (X : Syn) :
    AddCommGroup (BiHom m n X) :=
  inferInstance

/-- Bigraded suspension is tensoring with the corresponding sphere. -/
noncomputable def biShift_eq_tensor_Smn (m n : ℤ) (X : Syn) :
    (SyntheticCategory.biShift (m, n)).obj X ≅ Smn m n ⊗ X :=
  (SyntheticCategory.biShift (m, n)).mapIso (λ_ X).symm ≪≫
    SyntheticCategory.biShift_tensor_comm (m, n) (𝟙_ Syn) X

/-- Suspension invariance for bigraded homotopy classes. -/
noncomputable def susp_invariance (m n k l : ℤ) (X : Syn) :
    (BiHom m n X) ≃
      BiHom (m + k) (n + l) ((SyntheticCategory.biShift (k, l)).obj X) := by
  refine ((SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (k, l)).homEquiv).trans ?_
  exact Iso.homCongr
    ((SyntheticCategory.biShift_comp (m, n) (k, l)).app S00)
    (Iso.refl _)

/-- The λ-action on bigraded homotopy classes by precomposition. -/
noncomputable def lambdaAction (m n : ℤ) (X : Syn) :
    BiHom m n X → BiHom m (n - 1) X := by
  intro f
  have heq : (m, n) + (0, -1) = (m, n - 1) := by
    ext <;> simp [sub_eq_add_neg]
  refine eqToHom ?_ ≫
    (SyntheticCategory.biShift_comp (m, n) (0, -1)).inv.app S00 ≫
      SyntheticCategory.lam.app (Smn m n) ≫ f
  simp only [Smn]
  rw [heq]

end KIP126.Synthetic.Context
