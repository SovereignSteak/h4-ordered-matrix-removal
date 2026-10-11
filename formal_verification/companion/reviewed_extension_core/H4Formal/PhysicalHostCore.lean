import H4Formal.HostOrderCompression
import H4Formal.HostSizes
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0

abbrev PhysicalPosition (h : Nat) :=
  (Fin h × Fin 6 × Fin 2 × Fin (2 ^ h)) ⊕
    (Fin h × Fin 2 × Fin (2 ^ h)) ⊕ Fin (2 ^ h) ⊕ Fin (2 ^ h)

def physicalBlock (h : Nat) : PhysicalPosition h → Block
  | .inl ⟨d, mode, group, _⟩ =>
      .anchor (modeFromCode mode.val (d.val + 1)) (group.val + 1)
  | .inr (.inl ⟨d, sign, position⟩) =>
      .variable d.val (position.val / 2 ^ (h - d.val))
        (if sign.val = 0 then .plus else .minus)
  | .inr (.inr (.inl leaf)) => .variable h leaf.val .leaf
  | .inr (.inr (.inr _)) => .dummy

def physicalOffset (h : Nat) : PhysicalPosition h → Nat
  | .inl ⟨_, _, _, offset⟩ => offset.val
  | .inr (.inl ⟨d, _, position⟩) => position.val % 2 ^ (h - d.val)
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr offset)) => offset.val

def physicalBefore (h : Nat) (isRow : Bool) (r s : PhysicalPosition h) : Prop :=
  (physicalBlock h r = physicalBlock h s ∧ physicalOffset h r < physicalOffset h s) ∨
    hostComesBefore true isRow (physicalBlock h r) (physicalBlock h s) = true

abbrev PhysicalMatrix (h : Nat) := PhysicalPosition h → PhysicalPosition h → Bool

def physicalMatrix (h : Nat) (repair : Bool) : PhysicalMatrix h :=
  fun r c => (concreteHost h repair).value (physicalBlock h r) (physicalBlock h c)

def IsPhysicalCopy (h : Nat) (matrix : PhysicalMatrix h)
    (rows cols : Fin 4 → PhysicalPosition h) : Prop :=
  (∀ i j, i.val < j.val → physicalBefore h true (rows i) (rows j)) ∧
    (∀ i j, i.val < j.val → physicalBefore h false (cols i) (cols j)) ∧
    (∀ i j, matrix (rows i) (cols j) = pattern i j)

def IsPhysicalFree (h : Nat) (matrix : PhysicalMatrix h) : Prop :=
  ∀ rows cols, ¬ IsPhysicalCopy h matrix rows cols

def PhysicalCopies (h : Nat) (matrix : PhysicalMatrix h) :=
  { rc : (Fin 4 → PhysicalPosition h) × (Fin 4 → PhysicalPosition h) //
      IsPhysicalCopy h matrix rc.1 rc.2 }

noncomputable instance (h : Nat) (matrix : PhysicalMatrix h) :
    Fintype (PhysicalCopies h matrix) := by
  unfold PhysicalCopies
  exact Fintype.ofFinite _

theorem physicalPosition_card (h : Nat) :
    Fintype.card (PhysicalPosition h) = hostSideLength h := by
  simp only [PhysicalPosition, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    hostSideLength, branchFactor]
  ring

theorem level_factor (h d : Nat) (hd : d ≤ h) :
    2 ^ h = 2 ^ d * 2 ^ (h - d) := by
  rw [← Nat.pow_add, Nat.add_sub_of_le hd]

theorem physicalBlock_valid (h : Nat) (p : PhysicalPosition h) :
    validBlock h (physicalBlock h p) = true := by
  rcases p with ⟨d, mode, group, offset⟩ | (⟨d, sign, position⟩ | (leaf | offset))
  · have hm := allowed_mode_from_code mode.val (d.val + 1) (by omega)
    have hd := d.isLt
    have hg : group.val + 1 = 1 ∨ group.val + 1 = 2 := by omega
    simp only [physicalBlock, validBlock, mode_from_code_depth, hm,
      Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    exact ⟨⟨⟨by omega, by omega⟩, hg⟩, True.intro⟩
  · have hd := d.isLt
    have hn : position.val / 2 ^ (h - d.val) < 2 ^ d.val := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      rw [← level_factor h d.val (by omega)]
      exact position.isLt
    fin_cases sign <;>
      simp [physicalBlock, validBlock, Nat.ne_of_lt hd, hn, Nat.le_of_lt hd]
    all_goals decide
  · simp [physicalBlock, validBlock, leaf.isLt]
    rfl
  · rfl

theorem physical_copy_row_blocks_injective (h : Nat) (repair : Bool)
    (rows cols : Fin 4 → PhysicalPosition h)
    (hc : IsPhysicalCopy h (physicalMatrix h repair) rows cols) :
    Function.Injective (fun i => physicalBlock h (rows i)) := by
  intro i j he
  by_contra hij
  obtain ⟨k, hk⟩ := distinct_rows i j hij
  apply hk
  calc
    pattern i k = physicalMatrix h repair (rows i) (cols k) := (hc.2.2 i k).symm
    _ = physicalMatrix h repair (rows j) (cols k) := by simp only [physicalMatrix, he]
    _ = pattern j k := hc.2.2 j k

theorem physical_copy_col_blocks_injective (h : Nat) (repair : Bool)
    (rows cols : Fin 4 → PhysicalPosition h)
    (hc : IsPhysicalCopy h (physicalMatrix h repair) rows cols) :
    Function.Injective (fun i => physicalBlock h (cols i)) := by
  intro i j he
  by_contra hij
  obtain ⟨k, hk⟩ := distinct_columns i j hij
  apply hk
  calc
    pattern k i = physicalMatrix h repair (rows k) (cols i) := (hc.2.2 k i).symm
    _ = physicalMatrix h repair (rows k) (cols j) := by simp only [physicalMatrix, he]
    _ = pattern k j := hc.2.2 k j

theorem physical_copy_to_quotient (h : Nat) (repair : Bool)
    (rows cols : Fin 4 → PhysicalPosition h)
    (hc : IsPhysicalCopy h (physicalMatrix h repair) rows cols) :
    IsValidCopy h repair (fun i => physicalBlock h (rows i))
      (fun i => physicalBlock h (cols i)) := by
  constructor
  · intro b hb
    simp only [selectedRecords, List.mem_append, List.mem_ofFn] at hb
    rcases hb with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> apply physicalBlock_valid
  constructor
  · intro i j hij
    rcases hc.1 i j hij with he | ho
    · have hfin : i = j := physical_copy_row_blocks_injective h repair rows cols hc he.1
      subst j
      omega
    · exact ho
  constructor
  · intro i j hij
    rcases hc.2.1 i j hij with he | ho
    · have hfin : i = j := physical_copy_col_blocks_injective h repair rows cols hc he.1
      subst j
      omega
    · exact ho
  · exact hc.2.2

theorem quotient_copy_realizes (h : Nat) (repair : Bool)
    (rows cols : Fin 4 → PhysicalPosition h)
    (hc : IsValidCopy h repair (fun i => physicalBlock h (rows i))
      (fun i => physicalBlock h (cols i))) :
    IsPhysicalCopy h (physicalMatrix h repair) rows cols := by
  exact ⟨fun i j hij => Or.inr (hc.2.1 i j hij),
    fun i j hij => Or.inr (hc.2.2.1 i j hij), hc.2.2.2⟩

theorem physical_copy_quotient_iff (h : Nat) (repair : Bool)
    (rows cols : Fin 4 → PhysicalPosition h) :
    IsPhysicalCopy h (physicalMatrix h repair) rows cols ↔
      IsValidCopy h repair (fun i => physicalBlock h (rows i))
        (fun i => physicalBlock h (cols i)) :=
  ⟨physical_copy_to_quotient h repair rows cols, quotient_copy_realizes h repair rows cols⟩

end H4Formal
