import H4Formal
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.startsWith "H4Formal." && wasOriginallyTheorem env name then some name else none
  let names := names.mergeSort (fun a b => a.toString ≤ b.toString)
  let required := #[
    ``H4Formal.classification_exhaustive,
    ``H4Formal.classification_iff,
    ``H4Formal.canonical_standard_free,
    ``H4Formal.exact_copy_count,
    ``H4Formal.exact_edit_distance,
    ``H4Formal.orderedPosition_order_iff,
    ``H4Formal.normalized_copy_ratio_tendsto,
    ``H4Formal.no_polynomial_removal_bound,
    ``H4Formal.end_to_end_main_theorem]
  for name in required do
    unless wasOriginallyTheorem env name do
      throwError "Required compiled theorem is missing: {name}"
  -- Share Lean's visited set across roots; the whole dependency closure is audited once.
  let (_, closure) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in closure.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unapproved axiom {ax} in the compiled proof dependency closure"
  let rows := names.toArray.map fun name => Json.mkObj [
    ("name", toJson name.toString),
    ("dependency_closure_policy_pass", toJson true)]
  let report := Json.mkObj [
    ("status", toJson "END_TO_END_STANDARD_AXIOM_AUDIT_PASS"),
    ("theorem_declarations_audited", toJson names.length),
    ("approved_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("axioms_in_dependency_closure", toJson (closure.axioms.map Name.toString)),
    ("required_theorems", toJson (required.map Name.toString)),
    ("arbitrary_edit_lower_bound_compiled", toJson true),
    ("end_to_end_main_theorem_certified", toJson true),
    ("theorems", Json.arr rows)]
  liftIO <| IO.FS.createDirAll "evidence"
  liftIO <| IO.FS.writeFile "evidence/proof_audit.json" (report.pretty ++ "\n")
  logInfo m!"Audited {names.length} compiled theorem declarations; only standard axioms occur."
