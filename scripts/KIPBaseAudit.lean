import Lean

/-! Report the historical component's actual compiled axiom dependencies.
This is a disclosure report, not an extension of the KIP126 axiom allowlist.
Every new compatibility declaration must be free of historical assumptions.
-/

open Lean

namespace KIPBaseAudit

partial def modulesIn (dir : System.FilePath) : IO (Array Name) := do
  let mut result := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      result := result ++ (← modulesIn entry.path)
    else if entry.path.extension == some "lean" then
      result := result.push <| (entry.path.withExtension "").components.foldl
        Name.mkStr Name.anonymous
  return result

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Include types, proof/definition bodies, and inductive constructors. -/
def dependencies (env : Environment) (name : Name) : Array Name :=
  match env.checked.get.find? name with
  | some (.axiomInfo v) => v.type.getUsedConstants
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.ctorInfo v) => v.type.getUsedConstants
  | some (.recInfo v) => v.type.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
  | _ => #[]

/-- Build the reachable graph once and propagate axioms along reverse edges.
The worklists also handle constructor/type cycles without partial cached answers.
-/
def dependencyReport (env : Environment) (roots : Array Name) :
    Lean.NameMap (Array Name) := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut reverse : Lean.NameMap (Array Name) := {}
  let mut seeds : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if let some (.axiomInfo _) := env.checked.get.find? name then
      if !allowed.contains name then seeds := seeds.push name
    for dep in dependencies env name do
      reverse := reverse.insert dep ((reverse.find? dep).getD #[] |>.push name)
      if !seen.contains dep then pending := pending.push dep
  let mut taints : Lean.NameMap (Array Name) := {}
  for seed in seeds.qsort Name.lt do
    pending := #[seed]
    seen := {}
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      taints := taints.insert name ((taints.find? name).getD #[] |>.push seed)
      pending := pending ++ (reverse.find? name).getD #[]
  return taints

def report : CoreM (Json × Bool) := do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let mut declarations : Array Json := #[]
  let mut axioms : Array String := #[]
  let mut cleanBridge := true
  -- Filter by originating module before sorting; sorting every imported Mathlib
  -- declaration is expensive and does not contribute to this component's report.
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | some index =>
      match modules[index.toNat]? with
      | some moduleName =>
        if moduleName == `KIPBase || (`KIPBase).isPrefixOf moduleName then acc.push name else acc
      | none => acc
    | none => acc
  IO.eprintln s!"kipbase-audit: inspecting {names.size} historical declarations"
  let taints := dependencyReport env names
  for name in names.qsort Name.lt do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := modules[index.toNat]? | continue
    if moduleName != `KIPBase && !(`KIPBase).isPrefixOf moduleName then continue
    let disallowed := ((taints.find? name).getD #[]).map Name.toString
    if let some (.axiomInfo _) := env.find? name then
      axioms := axioms.push name.toString
    if (`KIPBase.Compatibility).isPrefixOf moduleName && !disallowed.isEmpty then
      cleanBridge := false
    declarations := declarations.push <| Json.mkObj
      [("name", toJson name.toString), ("module", toJson moduleName.toString),
       ("historicalAxioms", toJson disallowed)]
  return (Json.mkObj [("axioms", toJson axioms),
    ("declarations", toJson declarations), ("cleanCompatibility", toJson cleanBridge)],
    cleanBridge && !declarations.isEmpty)

end KIPBaseAudit

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules := #[`KIPBase] ++ (← KIPBaseAudit.modulesIn "KIPBase")
  let clean ← unsafe Lean.withImportModules
      (modules.map (fun n => { module := n })) {} (trustLevel := 1024) fun env => do
    let ((json, clean), _) ← Core.CoreM.toIO KIPBaseAudit.report
      (ctx := { fileName := "<kipbase-audit>", fileMap := default }) (s := { env := env })
    -- Names/strings can share imported module storage. Serialize while the
    -- environment is alive, before withImportModules releases its mapped regions.
    IO.println json.pretty
    return clean
  return if clean then 0 else 1
