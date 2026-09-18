import Mathlib.CategoryTheory.GradedObject

/-!
# Graded objects

KIP126 uses Mathlib's `CategoryTheory.GradedObject` directly.  This module is
an import boundary for the category of graded objects; it intentionally adds no
project-local synonym for it.
-/

namespace KIP126.Core.Algebra

open CategoryTheory

universe u v w

/-- A graded object is a family of objects indexed by its grading type. -/
example {C : Type u} [Category.{v} C] (ι : Type w) :
    CategoryTheory.GradedObject ι C = (ι → C) :=
  rfl

end KIP126.Core.Algebra
