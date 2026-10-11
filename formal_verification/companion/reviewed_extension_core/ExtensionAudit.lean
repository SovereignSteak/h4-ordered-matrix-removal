import H4Formal
import Lean.Util.CollectAxioms

open Lean Elab Command
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

run_cmd do
  let env ← getEnv
  let projectModule := fun (n : Name) => n == `H4Formal || n.toString.startsWith "H4Formal."
  let imported := env.header.moduleNames.filter projectModule
  let names := env.constants.toList.filterMap fun (n, _) => do
    let idx ← env.getModuleIdxFor? n
    let mod := env.header.moduleNames[idx.toNat]!
    if projectModule mod then some n else none
  let names := names.mergeSort (fun a b => a.toString ≤ b.toString)
  let theorems := names.filter (wasOriginallyTheorem env)
  let required := #[
    ``H4Formal.physical_pattern_copy_has_small_witness,
    ``H4Formal.matrix_pattern_copy_has_small_witness,
    ``H4Formal.physical_pattern_free_all_depth_iff_bounded,
    ``H4Formal.matrix_pattern_free_all_depth_iff_bounded,
    ``H4Formal.boundedPhysicalPatternFree_correct,
    ``H4Formal.permuted_matrix_edit_lower_bound,
    ``H4Formal.permuted_matrix_minimum_edit_lower_bound,
    ``H4Formal.blockFiber_card,
    ``H4Formal.physical_pattern_lifts_card]
  unless imported.size == 34 do
    throwError "Expected all 34 derived extension modules; imported {imported.size}."
  for name in required do
    unless wasOriginallyTheorem env name do
      throwError "Required compiled extension theorem is missing: {name}"
  for mod in imported do
    if mod.toString.startsWith "H4Formal.Certificates." || mod == `H4Formal.CertifiedQueries then
      throwError "Unexpected global certificate module in reduced closure: {mod}"
  let (_, closure) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in closure.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} in the complete derived-project declaration closure"
  let report := Json.mkObj [
    ("status", toJson "DERIVED_EXTENSION_ALL_DECLARATIONS_STANDARD_AXIOM_PASS"),
    ("scope", toJson "Reduced extension project only; not full companion or global H4 theorem route"),
    ("selection_policy", toJson "Defining module; all declarations including private/anonymous definitions and theorems"),
    ("project_modules_imported", toJson imported.size),
    ("project_declarations_audited", toJson names.length),
    ("project_theorems_audited", toJson theorems.length),
    ("approved_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("axioms_in_dependency_closure", toJson (closure.axioms.map Name.toString)),
    ("required_theorems", toJson (required.map Name.toString)),
    ("modules", toJson (imported.map Name.toString)),
    ("declarations", toJson (names.toArray.map Name.toString))]
  liftIO <| IO.FS.createDirAll "evidence"
  liftIO <| IO.FS.writeFile "evidence/extension_axiom_audit.json" (report.pretty ++ "\n")
  logInfo m!"Audited all {imported.size} derived extension modules: {names.length} declarations, {theorems.length} theorems; standard axioms only."
