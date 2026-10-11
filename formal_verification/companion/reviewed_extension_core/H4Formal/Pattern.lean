import Lean

/-!
# The fixed four-by-four forbidden pattern

The definition is a literal transcription of the pattern in the accompanying
H4 paper.  These statements are small, kernel-checkable finite claims.  They
do not depend on the SMT oracle or on external axioms.
-/

namespace H4Formal

def pattern (r c : Fin 4) : Bool :=
  match r.val, c.val with
  | 0, 0 => false
  | 0, 1 => true
  | 0, 2 => true
  | 0, 3 => false
  | 1, 0 => true
  | 1, 1 => false
  | 1, 2 => false
  | 1, 3 => true
  | 2, 0 => true
  | 2, 1 => false
  | 2, 2 => true
  | 2, 3 => false
  | 3, 0 => false
  | 3, 1 => true
  | 3, 2 => true
  | 3, 3 => true
  | _, _ => false

/-- Every two distinct row signatures differ in a column. -/
theorem distinct_rows :
    ∀ r s : Fin 4, r ≠ s → ∃ c : Fin 4, pattern r c ≠ pattern s c := by
  decide

/-- Every two distinct column signatures differ in a row. -/
theorem distinct_columns :
    ∀ c d : Fin 4, c ≠ d → ∃ r : Fin 4, pattern r c ≠ pattern r d := by
  decide

/-- The four diagonal entries, retained as an explicit regression invariant. -/
theorem diagonal_entries :
    pattern 0 0 = false ∧ pattern 1 1 = false ∧
    pattern 2 2 = true ∧ pattern 3 3 = true := by
  decide

end H4Formal
