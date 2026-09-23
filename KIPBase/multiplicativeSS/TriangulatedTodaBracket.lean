import KIPBase.Mathlib

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.Pretriangulated

noncomputable section

universe u v

/-- The axioms of a Toda bracket whose values are morphisms out of the
shifted source. -/
class ShiftedTodaBracket
    (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ] where
  relation : ∀ {X Y Z W : C},
    (X⟦(1 : ℤ)⟧ ⟶ W) → (X ⟶ Y) → (Y ⟶ Z) → (Z ⟶ W) → Prop
  composable : ∀ {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W},
    relation x f g h → f ≫ g = 0 ∧ g ≫ h = 0
  indeterminacy_left : ∀ {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W},
    relation x f g h → ∀ y : Y⟦(1 : ℤ)⟧ ⟶ W,
      relation (x + f⟦(1 : ℤ)⟧' ≫ y) f g h
  indeterminacy_right : ∀ {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W},
    relation x f g h → ∀ z : X⟦(1 : ℤ)⟧ ⟶ Z,
      relation (x + z ≫ h) f g h
  indeterminacy_complete : ∀ {X Y Z W : C} {x₁ x₂ : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W},
    relation x₁ f g h → relation x₂ f g h →
      ∃ (y : Y⟦(1 : ℤ)⟧ ⟶ W) (z : X⟦(1 : ℤ)⟧ ⟶ Z),
        x₁ - x₂ = f⟦(1 : ℤ)⟧' ≫ y + z ≫ h
  juggling : ∀ {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V},
    relation x f g h → h ≫ d = 0 →
      ∃ y : Y⟦(1 : ℤ)⟧ ⟶ V,
        relation y g h d ∧ x ≫ d = (-f⟦(1 : ℤ)⟧') ≫ y
  exists_relation : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W),
    f ≫ g = 0 → g ≫ h = 0 →
      ∃ x : X⟦(1 : ℤ)⟧ ⟶ W, relation x f g h

namespace TriangulatedTodaBracket

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
  [Pretriangulated C]

/-- The Toda relation obtained from a distinguished triangle beginning in
`f`.  Thus `x ∈ ⟨f,g,h⟩` means that `g` extends across a cone of `f`
and the composite of that extension with `h` factors through the connecting
morphism of the triangle. -/
def Relation {X Y Z W : C} (x : X⟦(1 : ℤ)⟧ ⟶ W)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) : Prop :=
  ∃ (Q : C) (i : Y ⟶ Q) (p : Q ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk f i p ∈ distTriang C ∧
      ∃ gbar : Q ⟶ Z, i ≫ gbar = g ∧ p ≫ x = gbar ≫ h

theorem composable {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) : f ≫ g = 0 ∧ g ≫ h = 0 := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  let T := Triangle.mk f i p
  have hfi : f ≫ i = 0 := by
    simpa [T] using comp_distTriang_mor_zero₁₂ T hT
  have hip : i ≫ p = 0 := by
    simpa [T] using comp_distTriang_mor_zero₂₃ T hT
  constructor
  · calc
      f ≫ g = (f ≫ i) ≫ gbar := by rw [← hg, Category.assoc]
      _ = 0 := by rw [hfi, zero_comp]
  · calc
      g ≫ h = i ≫ (gbar ≫ h) := by rw [← hg, Category.assoc]
      _ = (i ≫ p) ≫ x := by rw [← hx, Category.assoc]
      _ = 0 := by rw [hip, zero_comp]

theorem exists_relation {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) :
    ∃ x : X⟦(1 : ℤ)⟧ ⟶ W, Relation x f g h := by
  obtain ⟨Q, i, p, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f i p
  obtain ⟨gbar, hgbar⟩ := T.yoneda_exact₂ hT g hfg
  have hzero : i ≫ (gbar ≫ h) = 0 := by
    calc
      i ≫ (gbar ≫ h) = (i ≫ gbar) ≫ h := by simp only [Category.assoc]
      _ = g ≫ h := by simpa [T] using congrArg (fun t => t ≫ h) hgbar.symm
      _ = 0 := hgh
  obtain ⟨x, hx⟩ := T.yoneda_exact₃ hT (gbar ≫ h) hzero
  exact ⟨x, Q, i, p, hT, gbar, hgbar.symm, hx.symm⟩

theorem indeterminacy_left {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (y : Y⟦(1 : ℤ)⟧ ⟶ W) :
    Relation (x + f⟦(1 : ℤ)⟧' ≫ y) f g h := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  refine ⟨Q, i, p, hT, gbar, hg, ?_⟩
  have hpf : p ≫ f⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ (Triangle.mk f i p) hT
  calc
    p ≫ (x + f⟦(1 : ℤ)⟧' ≫ y) = p ≫ x + p ≫ (f⟦(1 : ℤ)⟧' ≫ y) := by
      simp only [Preadditive.comp_add]
    _ = p ≫ x + (p ≫ f⟦(1 : ℤ)⟧') ≫ y := by rw [Category.assoc]
    _ = p ≫ x := by rw [hpf, zero_comp, add_zero]
    _ = gbar ≫ h := hx

theorem indeterminacy_right {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx : Relation x f g h) (z : X⟦(1 : ℤ)⟧ ⟶ Z) :
    Relation (x + z ≫ h) f g h := by
  rcases hx with ⟨Q, i, p, hT, gbar, hg, hx⟩
  refine ⟨Q, i, p, hT, gbar + p ≫ z, ?_, ?_⟩
  · have hip : i ≫ p = 0 :=
      comp_distTriang_mor_zero₂₃ (Triangle.mk f i p) hT
    calc
      i ≫ (gbar + p ≫ z) = i ≫ gbar + i ≫ (p ≫ z) := by
        simp only [Preadditive.comp_add]
      _ = g + (i ≫ p) ≫ z := by rw [hg, Category.assoc]
      _ = g := by rw [hip, zero_comp, add_zero]
  · calc
      p ≫ (x + z ≫ h) = p ≫ x + p ≫ (z ≫ h) := by
        simp only [Preadditive.comp_add]
      _ = gbar ≫ h + (p ≫ z) ≫ h := by rw [hx, Category.assoc]
      _ = (gbar + p ≫ z) ≫ h := by simp only [Preadditive.add_comp]

theorem indeterminacy_complete {X Y Z W : C}
    {x₁ x₂ : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (hx₁ : Relation x₁ f g h) (hx₂ : Relation x₂ f g h) :
    ∃ (y : Y⟦(1 : ℤ)⟧ ⟶ W) (z : X⟦(1 : ℤ)⟧ ⟶ Z),
      x₁ - x₂ = f⟦(1 : ℤ)⟧' ≫ y + z ≫ h := by
  rcases hx₁ with ⟨Q₁, i₁, p₁, hT₁, g₁, hg₁, hx₁⟩
  rcases hx₂ with ⟨Q₂, i₂, p₂, hT₂, g₂, hg₂, hx₂⟩
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk f i₁ p₁) (Triangle.mk f i₂ p₂) hT₁ hT₂
    (𝟙 X) (𝟙 Y) (by simp)
  dsimp only [Triangle.mk] at c hc₁ hc₂
  have hi : i₁ ≫ c = i₂ := by simpa using hc₁
  have hp : p₁ = c ≫ p₂ := by simpa using hc₂
  let δ : Q₁ ⟶ Z := g₁ - c ≫ g₂
  have hδ : i₁ ≫ δ = 0 := by
    dsimp [δ]
    rw [Preadditive.comp_sub, hg₁, ← Category.assoc, hi, hg₂, sub_self]
  obtain ⟨z, hz⟩ := (Triangle.mk f i₁ p₁).yoneda_exact₃ hT₁ δ hδ
  dsimp only [Triangle.mk] at z hz
  have hp₂x₂ : p₁ ≫ x₂ = (c ≫ g₂) ≫ h := by
    rw [hp, Category.assoc, hx₂, ← Category.assoc]
  have hpzh : p₁ ≫ (z ≫ h) = δ ≫ h := by
    rw [← Category.assoc, ← hz]
  let e : X⟦(1 : ℤ)⟧ ⟶ W := x₁ - x₂ - z ≫ h
  have he : p₁ ≫ e = 0 := by
    dsimp [e]
    rw [Preadditive.comp_sub, Preadditive.comp_sub, hx₁, hp₂x₂, hpzh]
    dsimp [δ]
    rw [Preadditive.sub_comp]
    abel
  have hrot : (Triangle.mk f i₁ p₁).rotate ∈ distTriang C :=
    rot_of_distTriang (Triangle.mk f i₁ p₁) hT₁
  obtain ⟨y₀, hy₀⟩ := (Triangle.mk f i₁ p₁).rotate.yoneda_exact₃ hrot e he
  dsimp only [Triangle.mk, Triangle.rotate] at y₀ hy₀
  refine ⟨-y₀, z, ?_⟩
  have hy₀' : e = f⟦(1 : ℤ)⟧' ≫ (-y₀) := by
    simpa [Triangle.rotate] using hy₀
  calc
    x₁ - x₂ = e + z ≫ h := by dsimp [e]; abel
    _ = f⟦(1 : ℤ)⟧' ≫ (-y₀) + z ≫ h := by rw [hy₀']

theorem juggling [IsTriangulated C]
    {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
    (hx : Relation x f g h) (hhd : h ≫ d = 0) :
    ∃ y : Y⟦(1 : ℤ)⟧ ⟶ V,
      Relation y g h d ∧ x ≫ d = (-f⟦(1 : ℤ)⟧') ≫ y := by
  rcases hx with ⟨Q, i, p, hTf, gbar, hg, hx⟩
  let Tf := Triangle.mk f i p
  have hTfi : Tf.rotate ∈ distTriang C := rot_of_distTriang Tf hTf
  obtain ⟨K, v, w, hTbar⟩ := distinguished_cocone_triangle gbar
  obtain ⟨Qg, j, q, hTg⟩ := distinguished_cocone_triangle g
  let Tbar := Triangle.mk gbar v w
  let Tg := Triangle.mk g j q
  let O := CategoryTheory.Triangulated.someOctahedron hg hTfi hTbar hTg
  dsimp only [Tf, Tbar, Tg, Triangle.mk, Triangle.rotate] at O
  have hpm : p ≫ O.m₁ = gbar ≫ j := by
    simpa [Tf, Tbar, Tg, O] using O.comm₁
  have hmq : O.m₁ ≫ q = -f⟦(1 : ℤ)⟧' := by
    simpa [Tf, Tbar, Tg, O, Triangle.rotate] using O.comm₂
  have hgh : g ≫ h = 0 := (composable ⟨Q, i, p, hTf, gbar, hg, hx⟩).2
  obtain ⟨hbar₀, hhbar₀⟩ := Tg.yoneda_exact₂ hTg h hgh
  dsimp only [Tg, Triangle.mk] at hbar₀ hhbar₀
  let δ : X⟦(1 : ℤ)⟧ ⟶ W := x - O.m₁ ≫ hbar₀
  have hpδ : p ≫ δ = 0 := by
    dsimp [δ]
    rw [Preadditive.comp_sub, hx, ← Category.assoc, hpm, Category.assoc,
      ← hhbar₀, sub_self]
  obtain ⟨a, ha⟩ := Tf.rotate.yoneda_exact₃ hTfi δ hpδ
  dsimp only [Tf, Triangle.mk, Triangle.rotate] at a ha
  let hbar : Qg ⟶ W := hbar₀ + q ≫ a
  have hjhbar : j ≫ hbar = h := by
    have hjq : j ≫ q = 0 := by
      simpa [Tg] using comp_distTriang_mor_zero₂₃ Tg hTg
    dsimp [hbar]
    rw [Preadditive.comp_add, ← hhbar₀, ← Category.assoc, hjq, zero_comp, add_zero]
  have hmx : O.m₁ ≫ hbar = x := by
    dsimp [hbar]
    rw [Preadditive.comp_add, ← Category.assoc, hmq]
    rw [← ha]
    dsimp [δ]
    abel
  have hjhd : j ≫ (hbar ≫ d) = 0 := by
    rw [← Category.assoc, hjhbar, hhd]
  obtain ⟨y, hy⟩ := Tg.yoneda_exact₃ hTg (hbar ≫ d) hjhd
  dsimp only [Tg, Triangle.mk] at y hy
  refine ⟨y, ?_, ?_⟩
  · exact ⟨Qg, j, q, hTg, hbar, hjhbar, hy.symm⟩
  · calc
      x ≫ d = (O.m₁ ≫ hbar) ≫ d := by rw [hmx]
      _ = O.m₁ ≫ (hbar ≫ d) := Category.assoc _ _ _
      _ = O.m₁ ≫ (q ≫ y) := by rw [← hy]
      _ = (O.m₁ ≫ q) ≫ y := by rw [Category.assoc]
      _ = (-f⟦(1 : ℤ)⟧') ≫ y := by rw [hmq]

/-- The canonical shifted Toda bracket supplied by the Toda cone
construction in a triangulated category. -/
noncomputable def construction [IsTriangulated C] : ShiftedTodaBracket C where
  relation := Relation
  composable := composable
  indeterminacy_left := indeterminacy_left
  indeterminacy_right := indeterminacy_right
  indeterminacy_complete := indeterminacy_complete
  juggling := juggling
  exists_relation := exists_relation

/-- A triangulated category carries the canonical shifted Toda bracket
constructed from distinguished triangles. -/
noncomputable instance [IsTriangulated C] : ShiftedTodaBracket C := construction

end TriangulatedTodaBracket

end

end KIPBase.SpectralSequence
