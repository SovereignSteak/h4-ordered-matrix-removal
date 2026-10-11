import H4Formal.PhysicalOrder
import H4Formal.EditForcing
import Mathlib.Algebra.Field.Rat

namespace H4Formal

open scoped Classical

set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

abbrev BinaryMatrix (n : Nat) := Fin n → Fin n → Bool

def IsMatrixCopy {n : Nat} (matrix : BinaryMatrix n) (rows cols : Fin 4 → Fin n) : Prop :=
  StrictMono rows ∧ StrictMono cols ∧ ∀ i j, matrix (rows i) (cols j) = pattern i j

def IsMatrixFree {n : Nat} (matrix : BinaryMatrix n) : Prop :=
  ∀ rows cols, ¬ IsMatrixCopy matrix rows cols

def MatrixCopies {n : Nat} (matrix : BinaryMatrix n) :=
  { rc : (Fin 4 → Fin n) × (Fin 4 → Fin n) // IsMatrixCopy matrix rc.1 rc.2 }

noncomputable instance {n : Nat} (matrix : BinaryMatrix n) : Fintype (MatrixCopies matrix) := by
  unfold MatrixCopies
  exact Fintype.ofFinite _

noncomputable def matrixCopyCount {n : Nat} (matrix : BinaryMatrix n) : Nat :=
  Fintype.card (MatrixCopies matrix)

def matrixEditCount {n : Nat} (a b : BinaryMatrix n) : Nat :=
  (Finset.univ.filter (fun cell : Fin n × Fin n => a cell.1 cell.2 ≠ b cell.1 cell.2)).card

theorem zero_matrix_free (n : Nat) : IsMatrixFree (fun _ _ : Fin n => false) := by
  intro rows cols hc
  have he := hc.2.2 0 1
  contradiction

def MatrixFreeEditCount {n : Nat} (a : BinaryMatrix n) (k : Nat) : Prop :=
  ∃ b : BinaryMatrix n, IsMatrixFree b ∧ matrixEditCount a b = k

theorem matrixFreeEditCount_exists {n : Nat} (a : BinaryMatrix n) :
    ∃ k, MatrixFreeEditCount a k :=
  ⟨matrixEditCount a (fun _ _ => false), (fun _ _ => false), zero_matrix_free n, rfl⟩

noncomputable def minimumMatrixEditCount {n : Nat} (a : BinaryMatrix n) : Nat :=
  Nat.find (matrixFreeEditCount_exists a)

theorem minimumMatrixEditCount_spec {n : Nat} (a : BinaryMatrix n) :
    MatrixFreeEditCount a (minimumMatrixEditCount a) :=
  Nat.find_spec (matrixFreeEditCount_exists a)

noncomputable def matrixDistanceRat {n : Nat} (a : BinaryMatrix n) : Rat :=
  (minimumMatrixEditCount a : Rat) / (n : Rat) ^ 2

noncomputable def indexPhysicalMatrix (h : Nat) (matrix : PhysicalMatrix h) :
    BinaryMatrix (hostSideLength h) :=
  fun i j => matrix (physicalIndex h .row i) (physicalIndex h .column j)

noncomputable def physicalizeMatrix (h : Nat) (matrix : BinaryMatrix (hostSideLength h)) :
    PhysicalMatrix h :=
  fun r c => matrix ((physicalIndex h .row).symm r) ((physicalIndex h .column).symm c)

@[simp] theorem indexPhysicalMatrix_physicalize (h : Nat)
    (matrix : BinaryMatrix (hostSideLength h)) :
    indexPhysicalMatrix h (physicalizeMatrix h matrix) = matrix := by
  funext i j
  simp [indexPhysicalMatrix, physicalizeMatrix]

@[simp] theorem physicalizeMatrix_index (h : Nat) (matrix : PhysicalMatrix h) :
    physicalizeMatrix h (indexPhysicalMatrix h matrix) = matrix := by
  funext r c
  simp [indexPhysicalMatrix, physicalizeMatrix]

theorem indexPhysicalMatrix_copy_iff (h : Nat) (matrix : PhysicalMatrix h)
    (rows cols : Fin 4 → Fin (hostSideLength h)) :
    IsMatrixCopy (indexPhysicalMatrix h matrix) rows cols ↔
      IsPhysicalCopy h matrix (fun i => physicalIndex h .row (rows i))
        (fun i => physicalIndex h .column (cols i)) := by
  constructor
  · intro hc
    refine ⟨?_, ?_, hc.2.2⟩
    · intro i j hij
      exact (physicalIndex_before h .row _ _).mpr (hc.1 hij)
    · intro i j hij
      exact (physicalIndex_before h .column _ _).mpr (hc.2.1 hij)
  · intro hc
    refine ⟨?_, ?_, hc.2.2⟩
    · intro i j hij
      exact (physicalIndex_before h .row _ _).mp (hc.1 i j hij)
    · intro i j hij
      exact (physicalIndex_before h .column _ _).mp (hc.2.1 i j hij)

theorem indexPhysicalMatrix_free_iff (h : Nat) (matrix : PhysicalMatrix h) :
    IsMatrixFree (indexPhysicalMatrix h matrix) ↔ IsPhysicalFree h matrix := by
  constructor
  · intro hf rows cols hc
    let rows' := fun i => (physicalIndex h .row).symm (rows i)
    let cols' := fun i => (physicalIndex h .column).symm (cols i)
    apply hf rows' cols'
    apply (indexPhysicalMatrix_copy_iff h matrix rows' cols').mpr
    simpa [rows', cols'] using hc
  · intro hf rows cols hc
    exact hf _ _ ((indexPhysicalMatrix_copy_iff h matrix rows cols).mp hc)

noncomputable def indexedCopiesEquiv (h : Nat) (matrix : PhysicalMatrix h) :
    MatrixCopies (indexPhysicalMatrix h matrix) ≃ PhysicalCopies h matrix :=
  (Equiv.prodCongr (Equiv.piCongrRight (fun _ : Fin 4 => physicalIndex h .row))
    (Equiv.piCongrRight (fun _ : Fin 4 => physicalIndex h .column))).subtypeEquiv
      (fun rc => indexPhysicalMatrix_copy_iff h matrix rc.1 rc.2)

theorem indexPhysicalMatrix_copy_count (h : Nat) (matrix : PhysicalMatrix h) :
    matrixCopyCount (indexPhysicalMatrix h matrix) = Fintype.card (PhysicalCopies h matrix) :=
  Fintype.card_congr (indexedCopiesEquiv h matrix)

theorem indexPhysicalMatrix_edit_count (h : Nat) (a b : PhysicalMatrix h) :
    matrixEditCount (indexPhysicalMatrix h a) (indexPhysicalMatrix h b) = editCount h a b := by
  unfold matrixEditCount editCount editCells
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    ((Equiv.prodCongr (physicalIndex h .row) (physicalIndex h .column)).subtypeEquiv
      (fun _ => Iff.rfl))

end H4Formal
