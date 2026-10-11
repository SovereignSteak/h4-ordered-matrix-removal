import H4Formal.GlobalTheorems
import ExactTransversal

namespace H4Formal.ExactTransversal

/-- Unconditional exact transversal statement on the physical host. -/
theorem exact_physical_transversal (h : Nat) (hh : 1 ≤ h) :
    (diagonalCells h).Nodup ∧ HitsAll h (diagonalCells h) ∧
      (diagonalCells h).length = 2 ^ h ∧
      ∀ cells : List (Cell h), HitsAll h cells → 2 ^ h ≤ cells.length :=
  exact_transversal_of_exhaustion h hh (classification_exhaustive h hh)

/-- An attained minimum hitting set of size 2^h for the usual finite matrix,
with a lower bound against all finite lists of cells, including every set. -/
theorem exact_standard_transversal (h : Nat) (hh : 1 ≤ h) :
    (standardDiagonalCells h).Nodup ∧ StandardHitsAll h (standardDiagonalCells h) ∧
      (standardDiagonalCells h).length = 2 ^ h ∧
      ∀ cells : List (StandardCell h), StandardHitsAll h cells → 2 ^ h ≤ cells.length :=
  exact_standard_transversal_of_exhaustion h hh (classification_exhaustive h hh)

end H4Formal.ExactTransversal
