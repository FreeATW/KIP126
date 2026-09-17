# Informal Guide: Stable Homotopy Theory (§2)

This covers all files in `KIPBase/StableHomotopy/`.

## Mathlib Infrastructure Available

- Triangulated categories: `Mathlib.CategoryTheory.Triangulated.Triangulated` — `class IsTriangulated` with octahedral axiom
- `Pretriangulated`: `Mathlib.CategoryTheory.Triangulated.Pretriangulated` — distinguished triangles, shift functor
- `Triangle C`: structure with obj₁, obj₂, obj₃, morphisms, in `Mathlib.CategoryTheory.Triangulated.Basic`
- Symmetric monoidal: `Mathlib.CategoryTheory.Monoidal.Basic`

## Overall Approach

Stable homotopy theory is axiomatized — we don't construct spectra from first principles. Instead:
1. Postulate a category `𝒮` (the stable homotopy category — i.e. the homotopy category of spectra) with required structure
2. Axiomatize it directly as a triangulated category, not via a stable model category
3. Postulate key objects (sphere spectrum, HF₂) and their properties
4. Build everything as structures/axioms

Use `variable (𝒮 : Type*) [Category 𝒮] [Preadditive 𝒮] [HasShift 𝒮 ℤ] [Pretriangulated 𝒮]` etc.

## File-by-File Guide

### Basic.lean (§2)
Define the stable homotopy category (the homotopy category of spectra) and its key objects.
We axiomatize it directly as a triangulated category, bypassing model category machinery:

```
class StableHomotopyCategory (𝒮 : Type*) extends
    Category 𝒮, HasShift 𝒮 ℤ, Pretriangulated 𝒮 where
  -- Symmetric monoidal structure (smash product)
  smash : MonoidalCategory 𝒮
  -- Sphere spectrum (unit of monoidal structure)
  𝕊 : 𝒮
  sphere_is_unit : 𝕊 = 𝟙_ 𝒮
```

Define:
- `S (n : ℤ) : 𝒮` — n-sphere `Σⁿ 𝕊`
- `π (n : ℤ) (X : 𝒮) : AddCommGroup` — homotopy groups `[Sⁿ, X]`
- `πStar (X : 𝒮) : GradedObject ℤ AddCommGroupCat` — graded homotopy groups
- Smash product properties: `S m ∧ S n ≃ S (m + n)`
- Mapping spectra: `F(X, Y)` with `π_n F(X,Y) ≅ [Σⁿ X, Y]`
- Long exact sequence on homotopy groups from cofiber sequence (axiom)

### Cohomology.lean (§2.3)
Define:
- `HF₂ : 𝒮` — Eilenberg-MacLane spectrum (axiom: it exists)
- Homotopy of HF₂: `π₀(HF₂) ≅ ZMod 2`, `πₙ(HF₂) = 0` for n ≠ 0 (axiom)
- `SteenrodAlgebra` — `π_* F(HF₂, HF₂)` (stated as axiom, not constructed)
- `H (n : ℤ) (X : 𝒮) : Type` — mod 2 cohomology `[Σⁿ X, HF₂]`
- `HStar (X : 𝒮)` — total cohomology with A-module structure
- `HHomology (n : ℤ) (X : 𝒮)` — mod 2 homology `π_n(HF₂ ∧ X)`

### Adams.lean (§2.4)
Define:
- `AdamsSS (X : 𝒮) : SpectralSequence ...` — Adams SS for X (axiom)
- Bigrading `(s, t)`, differentials `d_r : E_r^{s,t} → E_r^{s+r, t+r-1}`
- Functoriality in X
- `AdamsFiltration (X : 𝒮) : Filtration (πStar X)` — Adams filtration
- Convergence: `E_∞^{s,t} ≅ F^s π_{t-s} X / F^{s+1} π_{t-s} X` (axiom)
- `AdamsFiltrationMaps (f : X ⟶ Y) : ℤ` — AF of a map
- Characterization: AF(f) ≥ k iff f factors through k maps zero on HF₂-homology
- E₂ elements are 2-torsion
