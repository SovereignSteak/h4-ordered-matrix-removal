import H4Formal.ValidHost
import H4Formal.Matrix

namespace H4Formal

def blockSize (h : Nat) : Block → Nat
  | .anchor _ _ => 2 ^ h
  | .dummy => 2 ^ h
  | .variable d _ _ => 2 ^ (h - d)

theorem blockSize_positive (h : Nat) (b : Block) : 0 < blockSize h b := by
  cases b <;> simp [blockSize, Nat.pow_pos]

/-- A physical position includes its block and its offset inside that block. -/
structure PhysicalPosition (h : Nat) where
  block : Block
  valid : ValidBlock h block
  offset : Nat
  offset_lt : offset < blockSize h block

def physicalBefore {h : Nat} (axis : Axis) (x y : PhysicalPosition h) : Prop :=
  blockBefore axis x.block y.block = true ∨
    (x.block = y.block ∧ x.offset < y.offset)

def physicalHost (h : Nat) (repair : Bool := false) :
    OrderedMatrix (PhysicalPosition h) (PhysicalPosition h) where
  value r c := if repair then repairedValue h r.block c.block else hostValue h r.block c.block
  rowBefore := physicalBefore .row
  colBefore := physicalBefore .column

def quotientHost (h : Nat) (repair : Bool) : OrderedBlockHost :=
  if repair then canonicalHost h else originalHost h

theorem quotient_value (h : Nat) (repair : Bool) (r c : PhysicalPosition h) :
    (physicalHost h repair).value r c = (quotientHost h repair).value r.block c.block := by
  cases repair <;> rfl

theorem physical_copy_rows_distinct_blocks (h : Nat) (repair : Bool)
    (r c : Fin 4 → PhysicalPosition h) (hc : MatrixCopy (physicalHost h repair) r c) :
    ∀ i j, i ≠ j → (r i).block ≠ (r j).block := by
  intro i j hne heq
  obtain ⟨k, hdiff⟩ := distinct_rows i j hne
  have he : (physicalHost h repair).value (r i) (c k) =
      (physicalHost h repair).value (r j) (c k) := by
    simp only [physicalHost]
    rw [heq]
  exact hdiff ((hc.2.2 i k).symm.trans (he.trans (hc.2.2 j k)))

theorem physical_copy_cols_distinct_blocks (h : Nat) (repair : Bool)
    (r c : Fin 4 → PhysicalPosition h) (hc : MatrixCopy (physicalHost h repair) r c) :
    ∀ i j, i ≠ j → (c i).block ≠ (c j).block := by
  intro i j hne heq
  obtain ⟨k, hdiff⟩ := distinct_columns i j hne
  have he : (physicalHost h repair).value (r k) (c i) =
      (physicalHost h repair).value (r k) (c j) := by
    simp only [physicalHost]
    rw [heq]
  exact hdiff ((hc.2.2 k i).symm.trans (he.trans (hc.2.2 k j)))

theorem physical_copy_projects (h : Nat) (repair : Bool)
    (r c : Fin 4 → PhysicalPosition h) (hc : MatrixCopy (physicalHost h repair) r c) :
    ValidCopy h (quotientHost h repair) (fun i => (r i).block) (fun j => (c j).block) := by
  refine ⟨fun i => (r i).valid, fun j => (c j).valid, ?_, ?_, ?_⟩
  · intro i j hij
    have hne : i ≠ j := by intro heq; subst j; omega
    have hblocks := physical_copy_rows_distinct_blocks h repair r c hc i j hne
    rcases hc.1 i j hij with hlt | ⟨heq, _⟩
    · cases repair <;> exact hlt
    · exact False.elim (hblocks heq)
  · intro i j hij
    have hne : i ≠ j := by intro heq; subst j; omega
    have hblocks := physical_copy_cols_distinct_blocks h repair r c hc i j hne
    rcases hc.2.1 i j hij with hlt | ⟨heq, _⟩
    · cases repair <;> exact hlt
    · exact False.elim (hblocks heq)
  · intro i j
    exact (quotient_value h repair (r i) (c j)).symm.trans (hc.2.2 i j)

def representative (h : Nat) (b : Block) (hb : ValidBlock h b) : PhysicalPosition h :=
  ⟨b, hb, 0, blockSize_positive h b⟩

theorem valid_copy_lifts (h : Nat) (repair : Bool) (r c : Fin 4 → Block)
    (hc : ValidCopy h (quotientHost h repair) r c) :
    MatrixCopy (physicalHost h repair)
      (fun i => representative h (r i) (hc.1 i))
      (fun j => representative h (c j) (hc.2.1 j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    left
    have hlt := hc.2.2.1 i j hij
    cases repair <;> exact hlt
  · intro i j hij
    left
    have hlt := hc.2.2.2.1 i j hij
    cases repair <;> exact hlt
  · intro i j
    rw [quotient_value]
    exact hc.2.2.2.2 i j

theorem physical_free_iff_quotient_free (h : Nat) (repair : Bool) :
    PatternFree (physicalHost h repair) ↔
      ∀ r c, ¬ ValidCopy h (quotientHost h repair) r c := by
  constructor
  · intro hf r c hc
    exact hf _ _ (valid_copy_lifts h repair r c hc)
  · intro hf r c hc
    exact hf _ _ (physical_copy_projects h repair r c hc)

theorem valid_copy_arbitrary_offsets (h : Nat) (repair : Bool)
    (r c : Fin 4 → PhysicalPosition h)
    (hc : ValidCopy h (quotientHost h repair) (fun i => (r i).block) (fun i => (c i).block)) :
    MatrixCopy (physicalHost h repair) r c := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    left
    have ho := hc.2.2.1 i j hij
    cases repair <;> exact ho
  · intro i j hij
    left
    have ho := hc.2.2.2.1 i j hij
    cases repair <;> exact ho
  · intro i j
    rw [quotient_value]
    exact hc.2.2.2.2 i j

theorem physical_copy_iff_valid_copy (h : Nat) (repair : Bool)
    (r c : Fin 4 → PhysicalPosition h) :
    MatrixCopy (physicalHost h repair) r c ↔
      ValidCopy h (quotientHost h repair) (fun i => (r i).block) (fun i => (c i).block) :=
  ⟨physical_copy_projects h repair r c, valid_copy_arbitrary_offsets h repair r c⟩

end H4Formal
