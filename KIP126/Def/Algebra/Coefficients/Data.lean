import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Field.ZMod

/-!
# Project coefficient conventions

These aliases make the mod--2 specialization used by the compiled Adams
interfaces explicit.  Generic Blueprint nodes continue to refer to Mathlib's
`ZMod` and `ModuleCat`; project nodes refer to the declarations below.
-/

namespace KIP126.Core.Algebra

/-- The project's mod--2 coefficient field. -/
abbrev F2 := ZMod 2

/-- The abelian category of modules over the project's mod--2 coefficient field. -/
abbrev F2ModuleCat := ModuleCat F2

end KIP126.Core.Algebra
