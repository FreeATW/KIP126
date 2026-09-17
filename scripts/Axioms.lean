import Lean

/-!
Compiled-environment axiom allowlist audit for the rendered project source root.
The initializer substitutes the namespace and source directory placeholders.
-/

open Lean

def auditedRoot : Name := `KIP126
def auditedDirectory : System.FilePath := "KIP126"
def rootLeanFile : System.FilePath := "KIP126.lean"

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def withImportedEnv {α} (modules : Array Name) (act : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules (modules.map (fun moduleName => { module := moduleName })) {}
    (trustLevel := 1024) fun env =>
      Prod.fst <$> Core.CoreM.toIO act
        (ctx := { fileName := "<axioms>", fileMap := default }) (s := { env := env })

def inAuditedLib (moduleName : Name) : Bool :=
  moduleName == auditedRoot || auditedRoot.isPrefixOf moduleName

def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name component => Name.mkStr name component)
    Name.anonymous

partial def collectLeanModules (directory : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in (← directory.readDir) do
    if (← entry.path.isDir) then
      modules := modules ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      modules := modules.push (pathToModule entry.path)
  return modules

def auditedModules : IO (Array Name) := do
  let modules ← collectLeanModules auditedDirectory
  if (← rootLeanFile.pathExists) then
    return #[auditedRoot] ++ modules
  return modules

abbrev AxiomCacheM := ReaderT Environment (StateM (Lean.NameMap Bool))

partial def reachesDisallowedAxiom (constantName : Name) : AxiomCacheM Bool := do
  if let some result := (← get).find? constantName then
    return result
  modify (·.insert constantName false)
  let env ← read
  let anyExpr (expressions : Array Expr) : AxiomCacheM Bool :=
    expressions.anyM fun expression => expression.getUsedConstants.anyM reachesDisallowedAxiom
  let result ← match env.checked.get.find? constantName with
    | some (.axiomInfo value) =>
        if !allowedAxioms.contains constantName then pure true else anyExpr #[value.type]
    | some (.defnInfo value) => anyExpr #[value.type, value.value]
    | some (.thmInfo value) => anyExpr #[value.type, value.value]
    | some (.opaqueInfo value) => anyExpr #[value.type, value.value]
    | some (.quotInfo _) => pure false
    | some (.ctorInfo value) => anyExpr #[value.type]
    | some (.recInfo value) => anyExpr #[value.type]
    | some (.inductInfo value) =>
        if (← anyExpr #[value.type]) then pure true else value.ctors.anyM reachesDisallowedAxiom
    | none => pure false
  modify (·.insert constantName result)
  return result

def audit : CoreM (Nat × Array String) := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  -- The historical migration has explicitly retained assumptions. Even a clean
  -- declaration must be ported into the canonical model before KIP126 imports it.
  if moduleNames.any (fun n => n == `KIPBase || (`KIPBase).isPrefixOf n) then
    return (0, #["KIP126 imports the isolated KIPBase historical component"])
  let candidates : Array Name := env.constants.fold (init := #[]) fun declarations declarationName _ =>
    match env.getModuleIdxFor? declarationName with
    | some index =>
      match moduleNames[index.toNat]? with
      | some moduleName =>
          if inAuditedLib moduleName then declarations.push declarationName else declarations
      | none => declarations
    | none => declarations
  let offenders : Array Name :=
    (candidates.filterM reachesDisallowedAxiom |>.run env).run' {}
  let mut messages : Array String := #[]
  for declarationName in offenders do
    let axioms ← collectAxioms declarationName
    let disallowed := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
    messages := messages.push s!"  {declarationName} → {disallowed.toList}"
  return (candidates.size, messages)

def main : IO UInt32 := do
  let modules ← auditedModules
  if modules.isEmpty then
    IO.eprintln s!"axioms: found no Lean modules under {auditedDirectory}: the audit is miswired."
    return 1
  let (audited, messages) ← withImportedEnv modules audit
  if audited == 0 && !messages.isEmpty then
    for message in messages do
      IO.eprintln message
    return 1
  if audited == 0 then
    IO.eprintln s!"axioms: audited 0 declarations in {auditedRoot}: the audit is miswired."
    return 1
  if messages.isEmpty then
    IO.println s!"axioms: audited {audited} {auditedRoot} declaration(s); all within the allowlist {allowedAxioms}."
    return 0
  IO.eprintln s!"axioms: {messages.size} declaration(s) in {auditedRoot} use disallowed axioms:"
  for message in messages do
    IO.eprintln message
  IO.eprintln s!"allowed: {allowedAxioms}"
  return 1
