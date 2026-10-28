import H4Formal.GlobalTheorems
import Lean.Util.CollectAxioms

-- Match the fixed 4×4 pattern in the manuscript, entry by entry.
example :
    H4Formal.pattern 0 0 = false ∧ H4Formal.pattern 0 1 = true ∧
    H4Formal.pattern 0 2 = true ∧ H4Formal.pattern 0 3 = false ∧
    H4Formal.pattern 1 0 = true ∧ H4Formal.pattern 1 1 = false ∧
    H4Formal.pattern 1 2 = false ∧ H4Formal.pattern 1 3 = true ∧
    H4Formal.pattern 2 0 = true ∧ H4Formal.pattern 2 1 = false ∧
    H4Formal.pattern 2 2 = true ∧ H4Formal.pattern 2 3 = false ∧
    H4Formal.pattern 3 0 = false ∧ H4Formal.pattern 3 1 = true ∧
    H4Formal.pattern 3 2 = true ∧ H4Formal.pattern 3 3 = true := by
  decide

-- The bound quantifies over every ordinary finite ordered Boolean matrix.
example (c C : ℝ) : H4Formal.PolynomialRemovalBound c C ↔
    ∀ (n : Nat) (D : Fin n → Fin n → Bool) (ε : ℝ),
      1 ≤ n → 0 < ε → ε ≤ 1 →
      ε ≤ (H4Formal.editDistance (H4Formal.numericMatrix D) : ℝ) / (n : ℝ) ^ 2 →
      c * ε ^ C ≤
        (H4Formal.matrixCopyCount (H4Formal.numericMatrix D) : ℝ) / (n : ℝ) ^ 8 :=
  Iff.rfl

example (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ¬ H4Formal.PolynomialRemovalBound c C :=
  H4Formal.no_polynomial_removal_bound c C hc hC

open Lean in
run_cmd do
  for name in [`H4Formal.no_polynomial_removal_bound,
      `H4Formal.end_to_end_main_theorem] do
    let axioms ← collectAxioms name
    for ax in axioms.toList do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unexpected axiom in {name}: {ax}"
    IO.println s!"AUDIT_AXIOMS_{name}={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"
