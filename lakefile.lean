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

@[default_target]
lean_lib KIP126 where
  globs := #[.andSubmodules `KIP126]

/-!
Historical KIP-base, ported to the pinned toolchain. Its inherited assumptions
are inventoried under migration/kip-base and must not enter KIP126's import graph.
-/
@[default_target]
lean_lib KIPBase where
  globs := #[.andSubmodules `KIPBase]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    -- Preserve the elaboration behavior used by the historical categorical proofs.
    -- These options affect elaboration only; the kernel and axiom audit are unchanged.
    ⟨`backward.defeqAttrib.useBackward, true⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩]

/-!
The trusted compiled-environment audit. Keep this target and its implementation
outside the worker-editable source overlay used by CI.
-/
lean_exe axioms where
  root := `scripts.Axioms

lean_exe kipbaseAudit where
  root := `scripts.KIPBaseAudit
