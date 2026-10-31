import Lean
import Lean.Util.CollectAxioms

/-!
# Foundational-axiom and public-import check

Every declaration originating in a project module is checked, including private
and generated declarations and declarations outside the project namespace.
Lean's collector follows transitive type and proof dependencies. The allowlist
is fixed; additional command-line modules are also audited and cannot replace
the public project import.
-/
open Lean

private def projectRoot : Name := `ProphetSecretary

private def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

private partial def sourceModules (dir : System.FilePath) (modulePrefix : Name) : IO (Array Name) := do
  let mut result := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      result := result ++ (← sourceModules entry.path (modulePrefix.str entry.fileName))
    else if entry.path.extension == some "lean" then
      result := result.push (modulePrefix.str entry.path.fileStem.get!)
  return result

private unsafe def audit (extra : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let additional := extra.toArray.map String.toName
  let imports := (#[projectRoot] ++ additional).map (fun n => ({ module := n } : Import))
  let env ← importModules imports {} (loadExts := true)
  let env := env.setExporting false
  let imported := env.header.moduleNames
  let sources ← sourceModules "ProphetSecretary" projectRoot
  let mut failures := 0
  for source in sources do
    unless imported.contains source do
      IO.eprintln s!"Public import does not reach {source}"
      failures := failures + 1
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | none => acc
    | some idx =>
      let owner := imported[idx.toNat]!
      if projectRoot.isPrefixOf owner || additional.any (·.isPrefixOf owner) then
        acc.push name
      else acc
  if names.isEmpty || sources.isEmpty then
    IO.eprintln "No project declarations or sources found; run this checker from the repository root."
    return 1
  let check : CoreM (Array (Name × Array Name)) := names.mapM fun name => do
    let axioms ← collectAxioms name
    return (name, axioms.filter (fun a => !allowedAxioms.contains a))
  let results ← check.toIO' { fileName := "scripts/CheckAxioms.lean", fileMap := FileMap.ofString "" }
    { env := env }
  for (name, forbidden) in results do
    unless forbidden.isEmpty do
      IO.eprintln s!"{name}: disallowed axioms {forbidden}"
      failures := failures + 1
  if failures > 0 then
    IO.eprintln s!"Verification failed ({failures} declaration/import violations)."
    return 1
  IO.println s!"Verified {names.size} project declarations in {sources.size} source modules."
  IO.println "Allowed axioms only: propext, Classical.choice, Quot.sound."
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  try
    audit args
  catch e =>
    IO.eprintln s!"Axiom check failed: {e}"
    return 1
