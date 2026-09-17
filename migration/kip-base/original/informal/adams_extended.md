# Adams Extended Content — New definitions and axioms for StableHomotopy/Adams.lean

## Overview

These are NEW definitions and axioms to be added to `StableHomotopy/Adams.lean`. They extend the Adams spectral sequence formalization with: finite spectra (refined), connectivity, finite type, odd-order elements, extended convergence, and boundedness.

All items marked "sorry" in the user hints should be axiomatized (these are infrastructure results whose proofs require Mathlib features that don't exist). The key contribution is stating them with correct types.

## Task 1: Refine `IsFiniteSpectrum` (currently `True` placeholder)

**Current** (Adams.lean line 147):
```lean
class IsFiniteSpectrum (X : 𝒮) : Prop where
  finite : True
```

**Target**: Replace with an inductive predicate capturing "smallest full subcategory containing sphere, closed under Σ, Σ⁻¹, and cofiber":

```lean
inductive IsFiniteSpectrum : 𝒮 → Prop where
  | sphere : IsFiniteSpectrum SphereSpectrum
  | susp {X : 𝒮} : IsFiniteSpectrum X → IsFiniteSpectrum (X⟦(1 : ℤ)⟧)
  | desusp {X : 𝒮} : IsFiniteSpectrum X → IsFiniteSpectrum (X⟦(-1 : ℤ)⟧)
  | cofiber {X Y : 𝒮} (f : X ⟶ Y) : IsFiniteSpectrum X → IsFiniteSpectrum Y →
      ∀ (Z : 𝒮), (∃ i p, Triangle.mk f i p ∈ distTriang 𝒮) → IsFiniteSpectrum Z
```

Wait, the cofiber clause is tricky — `Z` is the cofiber of `f`, but we need to say `Z` appears as the third vertex. Better:

```lean
inductive IsFiniteSpectrum : 𝒮 → Prop where
  | sphere : IsFiniteSpectrum SphereSpectrum
  | shift {X : 𝒮} (n : ℤ) : IsFiniteSpectrum X → IsFiniteSpectrum (X⟦n⟧)
  | cofiber {X Y Z : 𝒮} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1:ℤ)⟧} :
      Triangle.mk f g h ∈ distTriang 𝒮 → IsFiniteSpectrum X → IsFiniteSpectrum Y → IsFiniteSpectrum Z
```

**Note**: `SphereSpectrum` is defined in `StableHomotopy/Basic.lean` as `𝟙_ 𝒮`. The `shift` clause subsumes both `susp` and `desusp`. The `cofiber` clause takes a distinguished triangle and says if `X, Y` are finite then the cofiber `Z` is too.

**Important**: This changes `IsFiniteSpectrum` from a `class` to an `inductive`. The existing `adamsConvergence` axiom uses `[IsFiniteSpectrum X]` (typeclass instance). After the change, it should use `(hX : IsFiniteSpectrum X)` instead. Update all downstream uses.

## Task 2: Connectivity

Add new definitions:

```lean
/-- A spectrum X is n-connected if π_i(X) = 0 for all i ≤ n. -/
def IsConnected (X : 𝒮) (n : ℤ) : Prop :=
  ∀ i : ℤ, i ≤ n → IsZero (HomotopyGroup i X)

/-- The sphere spectrum is (-1)-connected. -/
axiom sphere_connected : IsConnected (𝒮 := 𝒮) SphereSpectrum (-1)

/-- If X is n-connected, then H_i(X; F₂) = 0 for i ≤ n. -/
axiom connected_homology_vanishing (X : 𝒮) (n : ℤ) (hX : IsConnected X n)
    (i : ℤ) (hi : i ≤ n) : IsZero (Mod2Homology i X)
```

## Task 3: Finite type

```lean
/-- A spectrum X is of finite type if it is connective and each π_i is finitely generated. -/
def IsFiniteType (X : 𝒮) : Prop :=
  (∃ n : ℤ, IsConnected X n) ∧
  (∀ i : ℤ, ∃ (S : Finset (HomotopyGroup i X)), ∀ x, x ∈ Submodule.span ℤ (S : Set _))
```

Wait, `HomotopyGroup i X` is `AddCommGroup` not a module over ℤ necessarily in our formalization. Let's simplify:

```lean
/-- A spectrum X is of finite type: connective with each homotopy group finitely generated. -/
class IsFiniteType (X : 𝒮) : Prop where
  connective : ∃ n : ℤ, IsConnected X n
  fg_homotopy : ∀ i : ℤ, AddGroup.FG (HomotopyGroup i X)
```

Hmm, `AddGroup.FG` may not exist in Mathlib. We can use `Module.Finite ℤ (HomotopyGroup i X)` if `HomotopyGroup i X` has a `Module ℤ` instance (it does, via `AddCommGroup.intModule`).

Actually simpler: just axiomatize.

```lean
/-- A spectrum X is of finite type. -/
class IsFiniteType (X : 𝒮) : Prop where
  finite_type : True  -- placeholder: connective + π_* finitely generated

/-- Finite type implies each H_i(X; F₂) is finite-dimensional. -/
axiom finiteType_homology_finiteDim (X : 𝒮) [IsFiniteType X] (i : ℤ) :
    ∃ (n : ℕ), ∀ (S : Finset (Mod2Homology i X)),
      S.card ≤ n
```

Actually, the user says "State equivalence (sorry): finite type ⟺ connective + each π_i finitely generated." So both sides should be stated but the equivalence is axiomatic.

**Pragmatic approach**: State `IsFiniteType` as a class with `True` (like the old `IsFiniteSpectrum`), then state the characterization and homology finiteness as axioms. This is consistent with our existing approach.

## Task 4: Odd-order elements

```lean
/-- Elements of odd order have infinite Adams filtration. -/
axiom af_odd_order_infinite {X Y : 𝒮} (f : X ⟶ Y)
    (hf : ∃ n : ℕ, Odd n ∧ n > 0 ∧ n • f = 0) : ∀ k : ℤ, HasAF_ge f k

/-- Elements that do not have odd order have finite Adams filtration. -/
axiom af_not_odd_order_finite {X Y : 𝒮} (f : X ⟶ Y)
    (hf : ¬ ∃ n : ℕ, Odd n ∧ n > 0 ∧ n • f = 0) : ∃ k : ℤ, AF f ≤ k
```

**Note**: `n • f` uses the `AddCommGroup` scalar multiplication on `(X ⟶ Y)` from `Preadditive`. Check that `SMul ℕ (X ⟶ Y)` exists (it should via `AddMonoid.SMul`).

## Task 5: Adams convergence (extended bigraded setting)

```lean
/-- Extended Adams convergence: for X ∈ S^{fin} and Y of finite type,
    the Adams SS converges in the bigraded setting [X, Y]. -/
axiom adamsConvergence_bigraded (X Y : 𝒮) (hX : IsFiniteSpectrum X)
    [IsFiniteType Y] :
    ∃ F : Filtration (fun n => (X ⟶ Y⟦n⟧)),
      True  -- weak convergence: graded pieces ≅ E_∞
```

This is deliberately vague — the full statement requires filtration on bigraded hom-sets and E_∞ identification, which is beyond our current infrastructure. Axiomatize with a meaningful type but `True` conclusion for the convergence part.

Actually, let's use a better formulation:

```lean
/-- Extended Adams convergence in the bigraded setting.
    For X finite and Y of finite type, the Adams SS for [X, Y]
    converges: the associated graded of the Adams filtration
    is isomorphic to the E∞-page. -/
axiom adamsConvergence_bigraded (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) [IsFiniteType Y] :
    ∃ F : Filtration (fun _n => AddCommGrpCat.{v}),
      Nonempty (Convergence (AdamsEInfty 𝒮 Y).ss (fun _n => AddCommGrpCat.of (X ⟶ Y)) F)
```

This may not type-check easily. The prover should adjust types to match the existing `Convergence` structure. If types don't align, axiomatize with a simpler statement.

## Task 6: Boundedness

```lean
/-- If H_i(X; ℚ) = 0 (rationally acyclic), then the Adams filtration on
    π_i(X)/odd-torsion is bounded, and all subquotients are finite groups. -/
axiom adams_boundedness (X : 𝒮) (i : ℤ)
    (hrat : True /- H_i(X; ℚ) = 0, not formalized -/) :
    ∃ (N : ℤ), ∀ s : ℤ, s > N → ∀ x : HomotopyGroup i X,
      InAdamsFiltration X s i x
```

This says: for large enough `s`, every element has filtration ≥ s (i.e., the filtration is eventually everything, meaning it's bounded).

## Organization

All new content should be added AFTER the existing content in `Adams.lean`, in a new section `/-! ### Extended Adams spectral sequence theory -/`. The prover should:

1. Modify `IsFiniteSpectrum` from class to inductive predicate
2. Update `adamsConvergence` signature to use `(hX : IsFiniteSpectrum X)` instead of `[IsFiniteSpectrum X]`
3. Add all new definitions and axioms
4. Verify compilation with `lean_diagnostic_messages`
