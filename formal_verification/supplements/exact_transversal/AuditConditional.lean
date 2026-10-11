import ExactTransversal
import Lean.Util.CollectAxioms

open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) => do
    let idx ← env.getModuleIdxFor? n
    if env.header.moduleNames[idx.toNat]! == `ExactTransversal then some n else none
  let names := names.mergeSort (fun a b => a.toString ≤ b.toString)
  let required := #[``H4Formal.ExactTransversal.exact_transversal_of_exhaustion,
    ``H4Formal.ExactTransversal.exact_standard_transversal_of_exhaustion,
    ``H4Formal.ExactTransversal.hitting_lower_bound,
    ``H4Formal.ExactTransversal.standard_hitting_lower_bound]
  for n in required do
    unless wasOriginallyTheorem env n do throwError "Missing theorem {n}"
  let (_, closure) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in closure.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  let report := Json.mkObj [
    ("status", toJson "CONDITIONAL_TRANSVERSAL_ALL_DECLARATIONS_STANDARD_AXIOM_PASS"),
    ("scope", toJson "ExactTransversal only; exhaustion premise is explicit and not discharged"),
    ("declarations_audited", toJson names.length),
    ("theorems_audited", toJson (names.filter (wasOriginallyTheorem env)).length),
    ("required_theorems", toJson (required.map Name.toString)),
    ("approved_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("axioms_in_dependency_closure", toJson (closure.axioms.map Name.toString)),
    ("imported_modules", toJson (env.header.moduleNames.map Name.toString)),
    ("declarations", toJson (names.toArray.map Name.toString))]
  liftIO <| IO.FS.createDirAll "evidence"
  liftIO <| IO.FS.writeFile "evidence/conditional_axiom_audit.json" (report.pretty ++ "\n")
  logInfo m!"Conditional exact transversal audited: {names.length} declarations"
