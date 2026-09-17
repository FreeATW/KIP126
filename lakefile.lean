import Lake
open Lake DSL

package KIP126 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

/-!
`leanblueprint checkdecls` shells out to this executable.  Pin the dependency
instead of following its default branch so declaration checking is reproducible.
-/
require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git" @
    "3d425859e73fcfbef85b9638c2a91708ef4a22d4"

/-- Independent statement definitions requested under `chanllege/`. -/
lean_lib Challenge where
  roots := #[`chanllege]
  globs := #[.submodules `chanllege]

@[default_target]
lean_lib KIP126 where
  globs := #[.andSubmodules `KIP126]

/-!
The trusted compiled-environment audit. Keep this target and its implementation
outside the worker-editable source overlay used by CI.
-/
lean_exe axioms where
  root := `scripts.Axioms
