import KIP126.Def.Algebra.Coefficients.Data
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Permanent classes in a concrete spectral sequence

Mathlib's categorical spectral sequence has no map from one page object to the
next: the next page is the homology of the current one.  For spectral sequences
of modules, this file makes the corresponding elementwise passage
explicit.  A page trajectory is a compatible choice of representatives on all
later pages.  A class is permanent when such a trajectory stays nonzero on
every page.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory
open KIP126.Core.Algebra

universe w u v

variable {R : Type u} [Ring R]

variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- The page reached after `n` successor steps from `r`. -/
def iteratedPage (r : ℤ) : ℕ → ℤ
  | 0 => r
  | n + 1 => iteratedPage r n + 1

@[simp] theorem iteratedPage_zero (r : ℤ) : iteratedPage r 0 = r := rfl

@[simp] theorem iteratedPage_succ (r : ℤ) (n : ℕ) :
    iteratedPage r (n + 1) = iteratedPage r n + 1 := rfl

/-- Every iterated page remains above the first displayed page. -/
theorem iteratedPage_ge {r : ℤ} (hr : r₀ ≤ r) :
    ∀ n : ℕ, r₀ ≤ iteratedPage r n
  | 0 => hr
  | n + 1 => by
      rw [iteratedPage_succ]
      exact (iteratedPage_ge hr n).trans (by omega)

/-- The class on the successor page represented by a cycle on page `r`. -/
noncomputable def nextPageClass
    (E : CategoryTheory.SpectralSequence (ModuleCat.{v} R) c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (p : κ)
    (x : (E.page r hr).X p)
    (hx : ((E.page r hr).d p ((c r).next p)) x = 0) :
    (E.page (r + 1) (hr.trans (by omega))).X p :=
  (E.iso r (r + 1) p rfl hr).hom
    ((E.page r hr).homologyπ p
      ((E.page r hr).cyclesMk x ((c r).next p) rfl hx))

/-- A compatible choice of the descendants of one page class on all successor
pages.  This structure by itself permits a descendant to become zero; the
predicate `IsPermanent` below rules that out. -/
structure PageTrajectory
    (E : CategoryTheory.SpectralSequence (ModuleCat.{v} R) c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (p : κ) (x : (E.page r hr).X p) where
  classAt : ∀ n : ℕ, (E.page (iteratedPage r n) (iteratedPage_ge hr n)).X p
  classAt_zero : classAt 0 = x
  isCycle : ∀ n : ℕ,
    ((E.page (iteratedPage r n) (iteratedPage_ge hr n)).d p
      ((c (iteratedPage r n)).next p)) (classAt n) = 0
  passage : ∀ n : ℕ,
    nextPageClass E (iteratedPage r n) (iteratedPage_ge hr n) p
      (classAt n) (isCycle n) = classAt (n + 1)

/-- A page class is permanent when it has compatible nonzero descendants on
every successor page.  This includes both halves of survival: it supports no
outgoing differential and is never killed by an incoming differential. -/
def IsPermanent
    (E : CategoryTheory.SpectralSequence (ModuleCat.{v} R) c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (p : κ) (x : (E.page r hr).X p) : Prop :=
  ∃ trajectory : PageTrajectory E r hr p x,
    ∀ n : ℕ, trajectory.classAt n ≠ 0

theorem IsPermanent.ne_zero
    {E : CategoryTheory.SpectralSequence (ModuleCat.{v} R) c r₀}
    {r : ℤ} {hr : r₀ ≤ r} {p : κ} {x : (E.page r hr).X p}
    (h : IsPermanent E r hr p x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨trajectory, hnonzero⟩ := h
  exact hnonzero 0 (trajectory.classAt_zero.trans rfl)

end KIP126.Core.SpectralSequence
