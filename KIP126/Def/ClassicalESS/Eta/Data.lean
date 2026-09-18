import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.Def.SpectralSequence.PageLevel.Data
import KIP126.External.Provenance
import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# The concrete classical eta extension spectral sequence

This is deliberately a paper-specific construction.  It returns Mathlib's
`CategoryTheory.SpectralSequence` and keeps the finite eta regression and its
set-valued detection relation in the concrete input, rather than extending the
shared spectral-sequence kernel with `Z`, `B`, or `E∞` fields.
-/

namespace KIP126.Classical.ExtensionSS

open CategoryTheory CategoryTheory.Limits
open KIP126.Classical.Adams
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence
open KIP126.External

abbrev Index := Bidegree
abbrev Coeff := F2ModuleCat

/-- The `(n,n)` differential shape of a classical eta-ESS page. -/
def etaESSShape (n : ℤ) : ComplexShape Index := ComplexShape.up' (n, n)

def etaESSPageLevel : PageLevelConvention where
  firstPage := 0
  admissibleFrom := 0
  page := fun r => r
  cycleLevel := fun r => r
  quotientExponent := fun r => r
  page_first := by norm_num
  page_succ := by intro r; norm_num
  cycle_succ := by intro r; norm_num
  quotient_succ := by intro r; norm_num
  cycleLevel_eq_quotientExponent := by intro r; rfl

/-- One named finite eta-ESS differential, retaining its source locator. -/
structure EtaDifferential where
  source : String
  target : String
  length : ℕ
  sourceDegree : Index
  targetDegree : Index
  sourceFiltration : ℤ
  targetFiltration : ℤ
  locator : Locator
  essential : Bool
  deriving DecidableEq, Repr, Inhabited

private def etaLocator (description : String) : Locator :=
  { description := description
    artifact := some "aimpaper/main.tex" }

def etaD₁ : EtaDifferential :=
  { source := "h₅d₀", target := "h₁h₅d₀", length := 1
    sourceDegree := (5, 51), targetDegree := (6, 52)
    sourceFiltration := 5, targetFiltration := 6
    locator := etaLocator "AIM Example 2.11, d₁ eta extension"
    essential := true }

def etaD₂ : EtaDifferential :=
  { source := "Δh₁g", target := "d₀l", length := 2
    sourceDegree := (9, 55), targetDegree := (11, 57)
    sourceFiltration := 9, targetFiltration := 11
    locator := etaLocator "AIM Example 2.11, d₂ eta extension"
    essential := true }

def etaD₃ : EtaDifferential :=
  { source := "h₁g₂", target := "Δh₂c₁", length := 3
    sourceDegree := (5, 51), targetDegree := (8, 54)
    sourceFiltration := 5, targetFiltration := 8
    locator := etaLocator "AIM Example 2.11, d₃ eta extension"
    essential := true }

def etaD₄ : EtaDifferential :=
  { source := "h₃²h₅", target := "Mh₁", length := 4
    sourceDegree := (3, 49), targetDegree := (7, 53)
    sourceFiltration := 3, targetFiltration := 7
    locator := etaLocator "AIM Example 2.11, d₄ eta extension"
    essential := true }

def etaD₂Inessential : EtaDifferential :=
  { source := "h₀h₃²h₅", target := "h₁h₅d₀", length := 2
    sourceDegree := (4, 50), targetDegree := (6, 52)
    sourceFiltration := 4, targetFiltration := 6
    locator := etaLocator "AIM Example 2.11, inessential d₂ eta extension"
    essential := false }

/-- The finite set of eta-extension rows used by the tracer bullet. -/
def etaESSDifferentials : Set EtaDifferential :=
  {etaD₁, etaD₂, etaD₃, etaD₄, etaD₂Inessential}

end KIP126.Classical.ExtensionSS

namespace KIP126.Classical.Regression

/-- The source-backed eta regression claim consumed by the concrete ESS. -/
def etaEss (rows : Set KIP126.Classical.ExtensionSS.EtaDifferential) : Prop :=
  rows = KIP126.Classical.ExtensionSS.etaESSDifferentials

end KIP126.Classical.Regression

namespace KIP126.Classical.ExtensionSS

open CategoryTheory CategoryTheory.Limits
open KIP126.Classical.Adams
open KIP126.Classical.Regression
open KIP126.External

/-! ### AIM-5 adapter and concrete page data -/

structure ClassicalEtaESSAdapter {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y) where
  sourceInfinity : GradedObject Index Coeff
  targetInfinity : GradedObject Index Coeff
  eta : AdamsClass source
  sourceClass : EtaDifferential → AdamsClass source
  targetClass : EtaDifferential → AdamsClass target
  sourceClass_degree : ∀ row, (sourceClass row).degree = row.sourceDegree
  targetClass_degree : ∀ row, (targetClass row).degree = row.targetDegree
  etaMap : ∀ b, sourceInfinity b ⟶ targetInfinity b
  rowMap : ∀ row : EtaDifferential,
    sourceInfinity row.sourceDegree ⊞ targetInfinity row.sourceDegree ⟶
      sourceInfinity row.targetDegree ⊞ targetInfinity row.targetDegree
  rowMap_nonzero : ∀ row, row ∈ etaESSDifferentials → rowMap row ≠ 0

noncomputable def E₀ {stable : StableHomotopyContext} {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}
    (A : ClassicalEtaESSAdapter source target) : GradedObject Index Coeff :=
  fun b => A.sourceInfinity b ⊞ A.targetInfinity b

/-! Concrete input retains the two AIM-5 Adams systems and exposes the finite
eta source/target classes through `rowMap`. -/

structure EtaESSPageData {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X}
    {target : ClassicalAdamsSS stable Y}
    (adapter : ClassicalEtaESSAdapter source target)
    (differentials : Set EtaDifferential) where
  d : ∀ (_n : ℤ) (i j : Index), E₀ adapter i ⟶ E₀ adapter j
  shape : ∀ (_n : ℤ) (i j : Index), ¬(etaESSShape _n).Rel i j → d _n i j = 0
  d_comp_d : ∀ (n : ℤ) (i j k : Index), d n i j ≫ d n j k = 0
  row : ∀ (row : EtaDifferential), row ∈ differentials →
    d row.length row.sourceDegree row.targetDegree = adapter.rowMap row

noncomputable def etaPage {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    {source : ClassicalAdamsSS stable X}
    {target : ClassicalAdamsSS stable Y}
    {adapter : ClassicalEtaESSAdapter source target}
    {differentials : Set EtaDifferential}
    (pageData : EtaESSPageData adapter differentials) (n : ℤ) :
    HomologicalComplex Coeff (etaESSShape n) where
  X := E₀ adapter
  d := pageData.d n
  shape := pageData.shape n
  d_comp_d' := by intro i j k hij hjk; exact pageData.d_comp_d n i j k

abbrev ClassicalEtaESS := SpectralSequence Coeff etaESSShape 0

def differentialDegree (n : ℕ) : Index := (n, n)

end KIP126.Classical.ExtensionSS
