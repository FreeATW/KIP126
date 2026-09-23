import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

/- multiplicativeSS 模块所需的外部数学依赖，统一收口到本文件，使
   `KIPBase/multiplicativeSS/` 各模块只依赖 KIP126/KIPBase 内部文件。 -/
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-! The mathematical dependencies of the historical library, replacing its
unrestricted `import Mathlib`. No additional assumptions or local instances. -/
