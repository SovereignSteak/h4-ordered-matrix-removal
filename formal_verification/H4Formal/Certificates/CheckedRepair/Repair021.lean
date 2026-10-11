import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair020

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair021_0 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((formula_660 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (formula_662 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ ((r3_kind = (2 : Int)) ∧ (r3_mode = (0 : Int)) ∧ (r3_level = (0 : Int)) ∧ (r3_group = (0 : Int)) ∧ (r3_depth = (0 : Int)) ∧ (r3_node = (0 : Int)) ∧ (r3_sign = (0 : Int))))
abbrev formula_664 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_0 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair021_1 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((formula_661 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (formula_663 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ ((r3_kind = (2 : Int)) ∧ (r3_mode = (0 : Int)) ∧ (r3_level = (0 : Int)) ∧ (r3_group = (0 : Int)) ∧ (r3_depth = (0 : Int)) ∧ (r3_node = (0 : Int)) ∧ (r3_sign = (0 : Int))))
abbrev formula_665 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_1 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_534 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ p1) ∧ (p2 ↔ p3)) → ((p0 ∨ p2 ∨ p4) ↔ (p1 ∨ p3 ∨ p4))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair021_2 (r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∧ (((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (((r3_level) ≤ (0 : Int)) ∧ (¬ ((r3_level) ≤ (-1 : Int)))) ∧ (((r3_group) ≤ (0 : Int)) ∧ (¬ ((r3_group) ≤ (-1 : Int)))) ∧ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) ∧ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int)))) ∧ (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))))
theorem normalization_2673 (r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((r3_kind = (2 : Int)) ∧ (r3_mode = (0 : Int)) ∧ (r3_level = (0 : Int)) ∧ (r3_group = (0 : Int)) ∧ (r3_depth = (0 : Int)) ∧ (r3_node = (0 : Int)) ∧ (r3_sign = (0 : Int))) ↔ (shared_expr_Repair021_2 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (and_congr (normalization_1256 r3_kind) (and_congr (normalization_2656 r3_mode) (and_congr (normalization_2657 r3_level) (and_congr (normalization_2658 r3_group) (and_congr (normalization_2649 r3_depth) (and_congr (normalization_2650 r3_node) (normalization_1259 r3_sign)))))))

abbrev shared_expr_Repair021_3 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (¬ ((r3_mode) ≤ (-1 : Int))) ∧ ((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_level) ≤ (0 : Int))) ∧ (¬ ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∨ (((r3_group) ≤ (2 : Int)) ∧ (¬ ((r3_group) ≤ (1 : Int))))) ∧ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) ∧ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int)))) ∧ (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))))
abbrev shared_expr_Repair021_4 (h r3_depth r3_sign : Int) : Prop := ((¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair021_5 (h r3_depth r3_sign : Int) : Prop := ((((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∨ (shared_expr_Repair021_4 h r3_depth r3_sign))
abbrev shared_expr_Repair021_6 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ (((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (((r3_level) ≤ (0 : Int)) ∧ (¬ ((r3_level) ≤ (-1 : Int)))) ∧ (((r3_group) ≤ (0 : Int)) ∧ (¬ ((r3_group) ≤ (-1 : Int)))) ∧ (¬ ((r3_depth) ≤ (-1 : Int))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ (¬ ((r3_node) ≤ (-1 : Int))) ∧ ((((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) → (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair021_5 h r3_depth r3_sign))
abbrev shared_expr_Repair021_7 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Repair021_3 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (shared_expr_Repair021_6 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (shared_expr_Repair021_2 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_2674 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_7 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (normalization_2651 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (or_congr (normalization_2668 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2673 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)))

abbrev shared_expr_Repair021_8 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (¬ ((r3_mode) ≤ (-1 : Int))) ∧ (¬ (¬ ((r3_mode) ≤ (5 : Int)))) ∧ (¬ ((r3_level) ≤ (0 : Int))) ∧ (¬ ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∨ (((r3_group) ≤ (2 : Int)) ∧ (¬ ((r3_group) ≤ (1 : Int))))) ∧ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) ∧ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int)))) ∧ (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))))
abbrev shared_expr_Repair021_9 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ (((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (((r3_level) ≤ (0 : Int)) ∧ (¬ ((r3_level) ≤ (-1 : Int)))) ∧ (((r3_group) ≤ (0 : Int)) ∧ (¬ ((r3_group) ≤ (-1 : Int)))) ∧ (¬ ((r3_depth) ≤ (-1 : Int))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ (¬ ((r3_node) ≤ (-1 : Int))) ∧ ((¬ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int))))) ∨ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair021_5 h r3_depth r3_sign))
abbrev shared_expr_Repair021_10 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Repair021_8 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (shared_expr_Repair021_9 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (shared_expr_Repair021_2 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_2675 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_665 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_10 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (normalization_2654 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (or_congr (normalization_2671 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2673 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)))

theorem normalization_2676 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_665 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ ((shared_expr_Repair021_7 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_10 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (iff_congr (normalization_2674 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2675 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_930 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_665 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  classical
  have ht := (normalized_534 (shared_expr_Repair021_3 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair021_8 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair021_6 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair021_9 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair021_2 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have n0 : ((shared_expr_Repair021_3 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_8 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
    exact Iff.mp (normalization_2655 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_928 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have n1 : ((shared_expr_Repair021_6 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_9 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
    exact Iff.mp (normalization_2672 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_929 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2676 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

abbrev shared_expr_Repair021_11 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((r3_kind = (2 : Int)) ∧ (r3_mode = (0 : Int)) ∧ (r3_level = (0 : Int)) ∧ (r3_group = (0 : Int)) ∧ (r3_depth = (0 : Int)) ∧ (r3_node = (0 : Int)) ∧ (r3_sign = (0 : Int))) ∨ (formula_661 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (formula_663 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_666 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_11 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_535 (p0 p1 p2 : Prop) : ((p0 ∨ p1 ∨ p2) ↔ (p2 ∨ p0 ∨ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair021_12 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Repair021_2 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (shared_expr_Repair021_8 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (shared_expr_Repair021_9 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_2677 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (normalization_2673 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (or_congr (normalization_2654 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2671 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)))

theorem normalization_2678 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_665 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ ((shared_expr_Repair021_10 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (iff_congr (normalization_2675 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2677 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_931 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_665 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  classical
  have ht := (normalized_535 (shared_expr_Repair021_8 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair021_9 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair021_2 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_2678 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

theorem normalized_536 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2679 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ ((shared_expr_Repair021_7 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (iff_congr (normalization_2674 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2677 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of trans.
theorem replay_932 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  classical
  have ht := (normalized_536 (shared_expr_Repair021_7 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair021_10 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have n0 : ((shared_expr_Repair021_7 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_10 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
    exact Iff.mp (normalization_2676 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_930 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have n1 : ((shared_expr_Repair021_10 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
    exact Iff.mp (normalization_2678 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_931 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2679 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_933 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) : (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_932 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) i93

theorem normalized_537 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2680 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ ((shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (iff_congr (normalization_2677 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2677 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_934 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  classical
  have ht := (normalized_537 (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_2680 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_935 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) : (formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_934 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_933 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93)

abbrev shared_expr_Repair021_13 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((r3_kind = (0 : Int)) ∧ (r3_mode ≥ (0 : Int)) ∧ (¬ (r3_mode ≥ (6 : Int))) ∧ (r3_level ≥ (1 : Int)) ∧ ((h + ((-1 : Int) * r3_level)) ≥ (0 : Int)) ∧ ((r3_group = (1 : Int)) ∨ (r3_group = (2 : Int))) ∧ (r3_depth = (0 : Int)) ∧ (r3_node = (0 : Int)) ∧ (r3_sign = (0 : Int)))
abbrev formula_667 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_13 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair021_14 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((r3_kind = (1 : Int)) ∧ (r3_mode = (0 : Int)) ∧ (r3_level = (0 : Int)) ∧ (r3_group = (0 : Int)) ∧ (r3_depth ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) ∧ (r3_node ≥ (0 : Int)) ∧ ((¬ (r3_depth = (0 : Int))) ∨ (r3_node = (0 : Int))) ∧ (((r3_depth = h) ∧ (r3_sign = (2 : Int))) ∨ ((¬ (r3_depth = h)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (1 : Int))))))
abbrev formula_668 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_14 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair021_15 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((r3_kind = (2 : Int)) ∧ (r3_mode = (0 : Int)) ∧ (r3_level = (0 : Int)) ∧ (r3_group = (0 : Int)) ∧ (r3_depth = (0 : Int)) ∧ (r3_node = (0 : Int)) ∧ (r3_sign = (0 : Int))) ∨ (formula_667 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (formula_668 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_669 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_15 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_538 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2681 (r3_mode : Int) : (r3_mode ≥ (6 : Int)) ↔ (¬ ((r3_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_2682 (r3_mode : Int) : (¬ (r3_mode ≥ (6 : Int))) ↔ (¬ (¬ ((r3_mode) ≤ (5 : Int)))) := (not_congr (normalization_2681 r3_mode))

theorem normalization_2683 (h r3_level : Int) : ((h + ((-1 : Int) * r3_level)) ≥ (0 : Int)) ↔ (¬ ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2684 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_667 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_8 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (and_congr (normalization_1241 r3_kind) (and_congr (normalization_2642 r3_mode) (and_congr (normalization_2682 r3_mode) (and_congr (normalization_2644 r3_level) (and_congr (normalization_2683 h r3_level) (and_congr (normalization_2648 r3_group) (and_congr (normalization_2649 r3_depth) (and_congr (normalization_2650 r3_node) (normalization_1259 r3_sign)))))))))

theorem normalization_2685 (h r3_depth : Int) : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) ↔ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2686 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_668 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_9 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (and_congr (normalization_1254 r3_kind) (and_congr (normalization_2656 r3_mode) (and_congr (normalization_2657 r3_level) (and_congr (normalization_2658 r3_group) (and_congr (normalization_2659 r3_depth) (and_congr (normalization_2685 h r3_depth) (and_congr (normalization_2661 r3_node) (and_congr (normalization_2670 r3_depth r3_node) (normalization_2667 h r3_depth r3_sign)))))))))

theorem normalization_2687 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_669 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (normalization_2673 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (or_congr (normalization_2684 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2686 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)))

theorem normalization_2688 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_669 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ ((shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (iff_congr (normalization_2677 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2687 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_936 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_666 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_669 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  classical
  have ht := (normalized_538 (shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_2688 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_937 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) : (formula_669 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_936 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_935 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93)

abbrev shared_expr_Repair021_16 (r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int))) ∨ (¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (r3_level ≤ (0 : Int))) ∨ (¬ (r3_level ≥ (0 : Int))) ∨ (¬ (r3_group ≤ (0 : Int))) ∨ (¬ (r3_group ≥ (0 : Int))) ∨ (¬ (r3_depth ≤ (0 : Int))) ∨ (¬ (r3_depth ≥ (0 : Int))) ∨ (¬ (r3_node ≤ (0 : Int))) ∨ (¬ (r3_node ≥ (0 : Int))) ∨ (¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))
abbrev formula_670 (r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_16 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair021_17 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((r3_mode ≥ (6 : Int)) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (r3_depth ≤ (0 : Int))) ∨ (¬ (r3_depth ≥ (0 : Int))) ∨ (¬ (r3_node ≤ (0 : Int))) ∨ (¬ (r3_node ≥ (0 : Int))) ∨ (¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (r3_kind ≤ (0 : Int))) ∨ (¬ (r3_kind ≥ (0 : Int))) ∨ (¬ (r3_level ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r3_group ≤ (1 : Int))) ∨ (¬ (r3_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_group ≤ (2 : Int))) ∨ (¬ (r3_group ≥ (2 : Int))))))))
abbrev formula_671 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_17 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair021_18 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((¬ (formula_670 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ∨ (¬ (formula_671 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ∨ (¬ (formula_659 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)))
abbrev formula_672 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_18 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_539 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p14 ∧ (¬ p15)) ∧ (¬ p3) ∧ (¬ (¬ p16)) ∧ (¬ p4) ∧ (¬ p17) ∧ ((p18 ∧ (¬ p6)) ∨ (p19 ∧ (¬ p18))) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p1 ∧ (¬ p14)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (¬ p9) ∧ (¬ p20) ∧ (¬ p11) ∧ ((¬ (p8 ∧ (¬ p9))) ∨ (p10 ∧ (¬ p11))) ∧ ((((¬ p20) ∧ p21) ∧ (p22 ∧ (¬ p23))) ∨ ((¬ ((¬ p20) ∧ p21)) ∧ ((p12 ∧ (¬ p13)) ∨ (p23 ∧ (¬ p12))))))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ p10) ∨ (¬ (¬ p11)) ∨ (¬ p12) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p16) ∨ (¬ (¬ p3)) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ p10) ∨ (¬ (¬ p11)) ∨ (¬ p12) ∨ (¬ (¬ p13)) ∨ (¬ p14) ∨ (¬ (¬ p15)) ∨ (¬ (¬ p4)) ∨ (¬ (¬ p17)) ∨ (¬ ((¬ ((¬ p18) ∨ (¬ (¬ p6)))) ∨ (¬ ((¬ p19) ∨ (¬ (¬ p18)))))))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ (¬ p9)) ∨ (¬ (¬ p11)) ∨ (¬ p1) ∨ (¬ (¬ p14)) ∨ (¬ (¬ p20)) ∨ (¬ ((¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ ((¬ p10) ∨ (¬ (¬ p11)))))) ∨ (¬ ((((¬ p21) ∨ (¬ (¬ p20))) ∧ ((¬ ((¬ p12) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p23) ∨ (¬ (¬ p12)))))) ∨ ((¬ ((¬ p21) ∨ (¬ (¬ p20)))) ∧ (¬ ((¬ p22) ∨ (¬ (¬ p23))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2689 (r3_mode : Int) : (r3_mode ≤ (0 : Int)) ↔ ((r3_mode) ≤ (0 : Int)) := by
  omega

theorem normalization_2690 (r3_mode : Int) : (¬ (r3_mode ≤ (0 : Int))) ↔ (¬ ((r3_mode) ≤ (0 : Int))) := (not_congr (normalization_2689 r3_mode))

theorem normalization_2691 (r3_mode : Int) : (¬ (r3_mode ≥ (0 : Int))) ↔ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) := (not_congr (normalization_2642 r3_mode))

theorem normalization_2692 (r3_level : Int) : (r3_level ≤ (0 : Int)) ↔ ((r3_level) ≤ (0 : Int)) := by
  omega

theorem normalization_2693 (r3_level : Int) : (¬ (r3_level ≤ (0 : Int))) ↔ (¬ ((r3_level) ≤ (0 : Int))) := (not_congr (normalization_2692 r3_level))

theorem normalization_2694 (r3_level : Int) : (r3_level ≥ (0 : Int)) ↔ (¬ ((r3_level) ≤ (-1 : Int))) := by
  omega

theorem normalization_2695 (r3_level : Int) : (¬ (r3_level ≥ (0 : Int))) ↔ (¬ (¬ ((r3_level) ≤ (-1 : Int)))) := (not_congr (normalization_2694 r3_level))

theorem normalization_2696 (r3_group : Int) : (r3_group ≤ (0 : Int)) ↔ ((r3_group) ≤ (0 : Int)) := by
  omega

theorem normalization_2697 (r3_group : Int) : (¬ (r3_group ≤ (0 : Int))) ↔ (¬ ((r3_group) ≤ (0 : Int))) := (not_congr (normalization_2696 r3_group))

theorem normalization_2698 (r3_group : Int) : (r3_group ≥ (0 : Int)) ↔ (¬ ((r3_group) ≤ (-1 : Int))) := by
  omega

theorem normalization_2699 (r3_group : Int) : (¬ (r3_group ≥ (0 : Int))) ↔ (¬ (¬ ((r3_group) ≤ (-1 : Int)))) := (not_congr (normalization_2698 r3_group))

theorem normalization_2700 (r3_depth : Int) : (r3_depth ≤ (0 : Int)) ↔ ((r3_depth) ≤ (0 : Int)) := by
  omega

theorem normalization_2701 (r3_depth : Int) : (¬ (r3_depth ≤ (0 : Int))) ↔ (¬ ((r3_depth) ≤ (0 : Int))) := (not_congr (normalization_2700 r3_depth))

theorem normalization_2702 (r3_depth : Int) : (¬ (r3_depth ≥ (0 : Int))) ↔ (¬ (¬ ((r3_depth) ≤ (-1 : Int)))) := (not_congr (normalization_2659 r3_depth))

theorem normalization_2703 (r3_node : Int) : (r3_node ≤ (0 : Int)) ↔ ((r3_node) ≤ (0 : Int)) := by
  omega

theorem normalization_2704 (r3_node : Int) : (¬ (r3_node ≤ (0 : Int))) ↔ (¬ ((r3_node) ≤ (0 : Int))) := (not_congr (normalization_2703 r3_node))

theorem normalization_2705 (r3_node : Int) : (¬ (r3_node ≥ (0 : Int))) ↔ (¬ (¬ ((r3_node) ≤ (-1 : Int)))) := (not_congr (normalization_2661 r3_node))

abbrev shared_expr_Repair021_19 (r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ ((r3_level) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_level) ≤ (-1 : Int)))) ∨ (¬ ((r3_group) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (-1 : Int)))) ∨ (¬ ((r3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_depth) ≤ (-1 : Int)))) ∨ (¬ ((r3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_node) ≤ (-1 : Int)))) ∨ (¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))
theorem normalization_2706 (r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_670 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_19 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (normalization_1382 r3_kind) (or_congr (normalization_1384 r3_kind) (or_congr (normalization_2690 r3_mode) (or_congr (normalization_2691 r3_mode) (or_congr (normalization_2693 r3_level) (or_congr (normalization_2695 r3_level) (or_congr (normalization_2697 r3_group) (or_congr (normalization_2699 r3_group) (or_congr (normalization_2701 r3_depth) (or_congr (normalization_2702 r3_depth) (or_congr (normalization_2704 r3_node) (or_congr (normalization_2705 r3_node) (or_congr (normalization_1405 r3_sign) (normalization_1407 r3_sign))))))))))))))

theorem normalization_2707 (r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (¬ (formula_670 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ (¬ (shared_expr_Repair021_19 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (not_congr (normalization_2706 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

theorem normalization_2708 (r3_level : Int) : (¬ (r3_level ≥ (1 : Int))) ↔ (¬ (¬ ((r3_level) ≤ (0 : Int)))) := (not_congr (normalization_2644 r3_level))

theorem normalization_2709 (h r3_level : Int) : (¬ ((h + ((-1 : Int) * r3_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_2683 h r3_level))

theorem normalization_2710 (r3_group : Int) : (r3_group ≤ (1 : Int)) ↔ ((r3_group) ≤ (1 : Int)) := by
  omega

theorem normalization_2711 (r3_group : Int) : (¬ (r3_group ≤ (1 : Int))) ↔ (¬ ((r3_group) ≤ (1 : Int))) := (not_congr (normalization_2710 r3_group))

theorem normalization_2712 (r3_group : Int) : (r3_group ≥ (1 : Int)) ↔ (¬ ((r3_group) ≤ (0 : Int))) := by
  omega

theorem normalization_2713 (r3_group : Int) : (¬ (r3_group ≥ (1 : Int))) ↔ (¬ (¬ ((r3_group) ≤ (0 : Int)))) := (not_congr (normalization_2712 r3_group))

theorem normalization_2714 (r3_group : Int) : ((¬ (r3_group ≤ (1 : Int))) ∨ (¬ (r3_group ≥ (1 : Int)))) ↔ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) := (or_congr (normalization_2711 r3_group) (normalization_2713 r3_group))

theorem normalization_2715 (r3_group : Int) : (¬ ((¬ (r3_group ≤ (1 : Int))) ∨ (¬ (r3_group ≥ (1 : Int))))) ↔ (¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) := (not_congr (normalization_2714 r3_group))

theorem normalization_2716 (r3_group : Int) : (r3_group ≤ (2 : Int)) ↔ ((r3_group) ≤ (2 : Int)) := by
  omega

theorem normalization_2717 (r3_group : Int) : (¬ (r3_group ≤ (2 : Int))) ↔ (¬ ((r3_group) ≤ (2 : Int))) := (not_congr (normalization_2716 r3_group))

theorem normalization_2718 (r3_group : Int) : (r3_group ≥ (2 : Int)) ↔ (¬ ((r3_group) ≤ (1 : Int))) := by
  omega

theorem normalization_2719 (r3_group : Int) : (¬ (r3_group ≥ (2 : Int))) ↔ (¬ (¬ ((r3_group) ≤ (1 : Int)))) := (not_congr (normalization_2718 r3_group))

theorem normalization_2720 (r3_group : Int) : ((¬ (r3_group ≤ (2 : Int))) ∨ (¬ (r3_group ≥ (2 : Int)))) ↔ ((¬ ((r3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (1 : Int))))) := (or_congr (normalization_2717 r3_group) (normalization_2719 r3_group))

theorem normalization_2721 (r3_group : Int) : (¬ ((¬ (r3_group ≤ (2 : Int))) ∨ (¬ (r3_group ≥ (2 : Int))))) ↔ (¬ ((¬ ((r3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (1 : Int)))))) := (not_congr (normalization_2720 r3_group))

theorem normalization_2722 (r3_group : Int) : ((¬ ((¬ (r3_group ≤ (1 : Int))) ∨ (¬ (r3_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_group ≤ (2 : Int))) ∨ (¬ (r3_group ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (1 : Int))))))) := (or_congr (normalization_2715 r3_group) (normalization_2721 r3_group))

theorem normalization_2723 (r3_group : Int) : (¬ ((¬ ((¬ (r3_group ≤ (1 : Int))) ∨ (¬ (r3_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_group ≤ (2 : Int))) ∨ (¬ (r3_group ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (1 : Int)))))))) := (not_congr (normalization_2722 r3_group))

abbrev shared_expr_Repair021_20 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ ((r3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_depth) ≤ (-1 : Int)))) ∨ (¬ ((r3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_node) ≤ (-1 : Int)))) ∨ (¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((r3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r3_level) ≤ (0 : Int)))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (1 : Int)))))))))
theorem normalization_2724 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_671 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_20 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (normalization_2681 r3_mode) (or_congr (normalization_2691 r3_mode) (or_congr (normalization_2701 r3_depth) (or_congr (normalization_2702 r3_depth) (or_congr (normalization_2704 r3_node) (or_congr (normalization_2705 r3_node) (or_congr (normalization_1405 r3_sign) (or_congr (normalization_1407 r3_sign) (or_congr (normalization_1348 r3_kind) (or_congr (normalization_1349 r3_kind) (or_congr (normalization_2708 r3_level) (or_congr (normalization_2709 h r3_level) (normalization_2723 r3_group)))))))))))))

theorem normalization_2725 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (¬ (formula_671 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ (¬ (shared_expr_Repair021_20 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (not_congr (normalization_2724 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

theorem normalization_2726 (r3_kind : Int) : (r3_kind ≤ (1 : Int)) ↔ ((r3_kind) ≤ (1 : Int)) := by
  omega

theorem normalization_2727 (r3_kind : Int) : (¬ (r3_kind ≤ (1 : Int))) ↔ (¬ ((r3_kind) ≤ (1 : Int))) := (not_congr (normalization_2726 r3_kind))

theorem normalization_2728 (r3_kind : Int) : (r3_kind ≥ (1 : Int)) ↔ (¬ ((r3_kind) ≤ (0 : Int))) := by
  omega

theorem normalization_2729 (r3_kind : Int) : (¬ (r3_kind ≥ (1 : Int))) ↔ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) := (not_congr (normalization_2728 r3_kind))

theorem normalization_2730 (h r3_depth : Int) : (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2685 h r3_depth))

theorem normalization_2731 (r3_node : Int) : ((¬ (r3_node ≤ (0 : Int))) ∨ (¬ (r3_node ≥ (0 : Int)))) ↔ ((¬ ((r3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_node) ≤ (-1 : Int))))) := (or_congr (normalization_2704 r3_node) (normalization_2705 r3_node))

theorem normalization_2732 (r3_node : Int) : (¬ ((¬ (r3_node ≤ (0 : Int))) ∨ (¬ (r3_node ≥ (0 : Int))))) ↔ (¬ ((¬ ((r3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_node) ≤ (-1 : Int)))))) := (not_congr (normalization_2731 r3_node))

theorem normalization_2733 (r3_depth r3_node : Int) : ((¬ (r3_depth ≤ (0 : Int))) ∨ (¬ (r3_depth ≥ (0 : Int))) ∨ (¬ ((¬ (r3_node ≤ (0 : Int))) ∨ (¬ (r3_node ≥ (0 : Int)))))) ↔ ((¬ ((r3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((r3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_node) ≤ (-1 : Int))))))) := (or_congr (normalization_2701 r3_depth) (or_congr (normalization_2702 r3_depth) (normalization_2732 r3_node)))

theorem normalization_2734 (r3_depth r3_node : Int) : (¬ ((¬ (r3_depth ≤ (0 : Int))) ∨ (¬ (r3_depth ≥ (0 : Int))) ∨ (¬ ((¬ (r3_node ≤ (0 : Int))) ∨ (¬ (r3_node ≥ (0 : Int))))))) ↔ (¬ ((¬ ((r3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((r3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_node) ≤ (-1 : Int)))))))) := (not_congr (normalization_2733 r3_depth r3_node))

theorem normalization_2735 (h r3_depth : Int) : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2736 (h r3_depth : Int) : (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (not_congr (normalization_2735 h r3_depth))

theorem normalization_2737 (h r3_depth : Int) : ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_2736 h r3_depth) (normalization_2730 h r3_depth))

theorem normalization_2738 (r3_sign : Int) : (r3_sign ≤ (1 : Int)) ↔ ((r3_sign) ≤ (1 : Int)) := by
  omega

theorem normalization_2739 (r3_sign : Int) : (¬ (r3_sign ≤ (1 : Int))) ↔ (¬ ((r3_sign) ≤ (1 : Int))) := (not_congr (normalization_2738 r3_sign))

theorem normalization_2740 (r3_sign : Int) : (r3_sign ≥ (1 : Int)) ↔ (¬ ((r3_sign) ≤ (0 : Int))) := by
  omega

theorem normalization_2741 (r3_sign : Int) : (¬ (r3_sign ≥ (1 : Int))) ↔ (¬ (¬ ((r3_sign) ≤ (0 : Int)))) := (not_congr (normalization_2740 r3_sign))

theorem normalization_2742 (r3_sign : Int) : ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) ↔ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))) := (or_congr (normalization_2739 r3_sign) (normalization_2741 r3_sign))

theorem normalization_2743 (r3_sign : Int) : (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_2742 r3_sign))

theorem normalization_2744 (r3_sign : Int) : ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))))) := (or_congr (normalization_1409 r3_sign) (normalization_2743 r3_sign))

theorem normalization_2745 (r3_sign : Int) : (r3_sign ≤ (2 : Int)) ↔ ((r3_sign) ≤ (2 : Int)) := by
  omega

theorem normalization_2746 (r3_sign : Int) : (¬ (r3_sign ≤ (2 : Int))) ↔ (¬ ((r3_sign) ≤ (2 : Int))) := (not_congr (normalization_2745 r3_sign))

theorem normalization_2747 (r3_sign : Int) : (r3_sign ≥ (2 : Int)) ↔ (¬ ((r3_sign) ≤ (1 : Int))) := by
  omega

theorem normalization_2748 (r3_sign : Int) : (¬ (r3_sign ≥ (2 : Int))) ↔ (¬ (¬ ((r3_sign) ≤ (1 : Int)))) := (not_congr (normalization_2747 r3_sign))

theorem normalization_2749 (r3_sign : Int) : ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))) ↔ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))) := (or_congr (normalization_2746 r3_sign) (normalization_2748 r3_sign))

theorem normalization_2750 (r3_sign : Int) : (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))) ↔ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))) := (not_congr (normalization_2749 r3_sign))

abbrev shared_expr_Repair021_21 (h r3_depth r3_sign : Int) : Prop := (((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))))))
abbrev shared_expr_Repair021_22 (h r3_depth r3_sign : Int) : Prop := ((shared_expr_Repair021_21 h r3_depth r3_sign) ∨ ((¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))))
theorem normalization_2751 (h r3_depth r3_sign : Int) : (formula_647 h r3_depth r3_sign) ↔ (shared_expr_Repair021_22 h r3_depth r3_sign) := (or_congr (and_congr (normalization_2737 h r3_depth) (normalization_2744 r3_sign)) (and_congr (not_congr (normalization_2737 h r3_depth)) (normalization_2750 r3_sign)))

theorem normalization_2752 (h r3_depth r3_sign : Int) : (¬ (formula_647 h r3_depth r3_sign)) ↔ (¬ (shared_expr_Repair021_22 h r3_depth r3_sign)) := (not_congr (normalization_2751 h r3_depth r3_sign))

abbrev shared_expr_Repair021_23 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ ((r3_level) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_level) ≤ (-1 : Int)))) ∨ (¬ ((r3_group) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r3_depth) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r3_node) ≤ (-1 : Int)))) ∨ (¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((r3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((r3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_node) ≤ (-1 : Int)))))))) ∨ (¬ (shared_expr_Repair021_22 h r3_depth r3_sign)))
theorem normalization_2753 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_659 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_23 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (normalization_2690 r3_mode) (or_congr (normalization_2691 r3_mode) (or_congr (normalization_2693 r3_level) (or_congr (normalization_2695 r3_level) (or_congr (normalization_2697 r3_group) (or_congr (normalization_2699 r3_group) (or_congr (normalization_2702 r3_depth) (or_congr (normalization_2705 r3_node) (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_2730 h r3_depth) (or_congr (normalization_2734 r3_depth r3_node) (normalization_2752 h r3_depth r3_sign)))))))))))))

theorem normalization_2754 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (¬ (formula_659 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ (¬ (shared_expr_Repair021_23 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (not_congr (normalization_2753 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

abbrev shared_expr_Repair021_24 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((¬ (shared_expr_Repair021_19 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ∨ (¬ (shared_expr_Repair021_20 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ∨ (¬ (shared_expr_Repair021_23 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)))
theorem normalization_2755 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_672 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_24 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (normalization_2707 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (or_congr (normalization_2725 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2754 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)))

theorem normalization_2756 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_669 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_672 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ ((shared_expr_Repair021_12 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair021_24 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (iff_congr (normalization_2687 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2755 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_938 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_669 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_672 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  classical
  have ht := (normalized_539 ((r3_kind) ≤ (2 : Int)) ((r3_kind) ≤ (1 : Int)) ((r3_mode) ≤ (0 : Int)) ((r3_mode) ≤ (-1 : Int)) ((r3_level) ≤ (0 : Int)) ((r3_level) ≤ (-1 : Int)) ((r3_group) ≤ (0 : Int)) ((r3_group) ≤ (-1 : Int)) ((r3_depth) ≤ (0 : Int)) ((r3_depth) ≤ (-1 : Int)) ((r3_node) ≤ (0 : Int)) ((r3_node) ≤ (-1 : Int)) ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((r3_kind) ≤ (0 : Int)) ((r3_kind) ≤ (-1 : Int)) ((r3_mode) ≤ (5 : Int)) ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((r3_group) ≤ (1 : Int)) ((r3_group) ≤ (2 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2756 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_939 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) : (formula_672 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_938 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_937 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93)

theorem propositional_540 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p8) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_940 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_671 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (r3_kind ≤ (0 : Int))) := by
  exact (propositional_540 (r3_mode ≥ (6 : Int)) (r3_mode ≥ (0 : Int)) (r3_depth ≤ (0 : Int)) (r3_depth ≥ (0 : Int)) (r3_node ≤ (0 : Int)) (r3_node ≥ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_kind ≤ (0 : Int)) (r3_kind ≥ (0 : Int)) (r3_level ≥ (1 : Int)) ((h + ((-1 : Int) * r3_level)) ≥ (0 : Int)) (r3_group ≤ (1 : Int)) (r3_group ≥ (1 : Int)) (r3_group ≤ (2 : Int)) (r3_group ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_941 (r3_kind : Int) : ((¬ (r3_kind ≤ (0 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair021_25 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_node % (2 : Int)) ≥ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))
abbrev formula_673 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_25 c2_level r3_depth r3_kind r3_node r3_sign)

theorem propositional_541 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_942 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : ((formula_673 c2_level r3_depth r3_kind r3_node r3_sign) ∨ (r3_kind ≥ (1 : Int))) := by
  exact (propositional_541 (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((r3_node % (2 : Int)) ≥ (1 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

abbrev shared_expr_Repair021_26 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_673 c2_level r3_depth r3_kind r3_node r3_sign))))
abbrev formula_674 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_26 c2_group c2_level r3_depth r3_kind r3_node r3_sign)

theorem propositional_542 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_943 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (¬ (formula_673 c2_level r3_depth r3_kind r3_node r3_sign))) := by
  exact (propositional_542 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r3_kind ≤ (2 : Int)) (r3_kind ≥ (2 : Int)) (formula_673 c2_level r3_depth r3_kind r3_node r3_sign))

theorem propositional_543 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_944 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : (((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign))) ∨ (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign)) := by
  exact (propositional_543 (c2_mode ≤ (3 : Int)) (c2_mode ≥ (3 : Int)) (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair021_27 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))
abbrev formula_675 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair021_27 c2_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair021_28 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))
abbrev formula_676 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair021_28 c2_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair021_29 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ (formula_675 c2_level r3_depth r3_kind r3_sign))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_676 c2_level r3_depth r3_kind r3_sign))))
abbrev formula_677 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair021_29 c2_group c2_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair021_30 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))
abbrev formula_678 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair021_30 c2_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair021_31 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))
abbrev formula_679 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair021_31 c2_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair021_32 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ (formula_678 c2_level r3_depth r3_kind r3_sign))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_679 c2_level r3_depth r3_kind r3_sign))))
abbrev formula_680 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair021_32 c2_group c2_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair021_33 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))
abbrev formula_681 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_33 c2_level r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair021_34 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_681 c2_level r3_depth r3_kind r3_node r3_sign))))
abbrev formula_682 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_34 c2_group c2_level r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair021_35 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))
abbrev formula_683 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_35 c2_level r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair021_36 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_683 c2_level r3_depth r3_kind r3_node r3_sign))))
abbrev formula_684 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_36 c2_group c2_level r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair021_37 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_node % (2 : Int)) ≥ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))
abbrev formula_685 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_37 c2_level r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair021_38 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_685 c2_level r3_depth r3_kind r3_node r3_sign))))
abbrev formula_686 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_38 c2_group c2_level r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair021_39 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_680 c2_group c2_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_682 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))))
abbrev formula_687 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_39 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair021_40 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) ∨ (¬ ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_680 c2_group c2_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_682 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))))
abbrev formula_688 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_40 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)

theorem propositional_544 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_945 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : (formula_688 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) := by
  exact (propositional_544 ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign))) ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_680 c2_group c2_level r3_depth r3_kind r3_sign))) ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_682 c2_group c2_level r3_depth r3_kind r3_node r3_sign))) ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign))) ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign))) ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign))))

theorem propositional_545 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_946 (c2_group c2_level c2_mode r3_depth r3_kind r3_sign : Int) : (((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_680 c2_group c2_level r3_depth r3_kind r3_sign))) ∨ (c2_mode ≤ (1 : Int))) := by
  exact (propositional_545 (c2_mode ≤ (1 : Int)) (c2_mode ≥ (1 : Int)) (c2_group ≤ (1 : Int)) (c2_group ≥ (1 : Int)) (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

-- Checked replay of th-lemma.
theorem replay_947 (c2_mode : Int) : ((c2_mode ≥ (2 : Int)) ∨ (¬ (c2_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_546 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ ((¬ ((¬ p8) ∨ (¬ p9))) ∨ (¬ ((¬ p10) ∨ (¬ p11))))) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_948 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ∨ (c2_mode ≥ (3 : Int))) := by
  exact (propositional_546 (c2_mode ≤ (3 : Int)) (c2_mode ≥ (3 : Int)) (c2_group ≤ (1 : Int)) (c2_group ≥ (1 : Int)) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_949 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : (c2_mode ≥ (3 : Int)) := by
  exact (Or.elim (replay_948 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (i81 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_950 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : (c2_mode ≥ (2 : Int)) := by
  exact (Or.elim (replay_947 c2_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_949 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i81)))))

-- Checked replay of unit-resolution.
theorem replay_951 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : (¬ (c2_mode ≤ (1 : Int))) := by
  exact (Or.elim (replay_223 c2_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_950 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i81)))))

-- Checked replay of unit-resolution.
theorem replay_952 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_680 c2_group c2_level r3_depth r3_kind r3_sign))) := by
  exact (Or.elim (replay_946 c2_group c2_level c2_mode r3_depth r3_kind r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_951 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i81) t0))))

theorem propositional_547 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ ((¬ ((¬ p8) ∨ (¬ p9))) ∨ (¬ ((¬ p10) ∨ (¬ p11))))) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_953 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : (((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_682 c2_group c2_level r3_depth r3_kind r3_node r3_sign))) ∨ (c2_mode ≤ (2 : Int))) := by
  exact (propositional_547 (c2_mode ≤ (2 : Int)) (c2_mode ≥ (2 : Int)) (c2_group ≤ (1 : Int)) (c2_group ≥ (1 : Int)) (r3_kind ≤ (2 : Int)) (r3_kind ≥ (2 : Int)) (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((r3_node % (2 : Int)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_954 (c2_mode : Int) : ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_955 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : (¬ (c2_mode ≤ (2 : Int))) := by
  exact (Or.elim (replay_954 c2_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_949 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i81)))))

-- Checked replay of unit-resolution.
theorem replay_956 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_682 c2_group c2_level r3_depth r3_kind r3_node r3_sign))) := by
  exact (Or.elim (replay_953 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_955 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i81) t0))))

-- Checked replay of unit-resolution.
theorem replay_957 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) := by
  exact (Or.elim (replay_945 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim (l0 i94))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i95))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_952 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_sign i81)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_956 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i81)))) (fun t3 => (Or.elim t3 (fun l4 => l4) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i96))) (fun t5 => (False.elim (t5 i97))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_958 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (formula_674 c2_group c2_level r3_depth r3_kind r3_node r3_sign) := by
  exact (Or.elim (replay_944 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim ((replay_957 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i81 i95 i96 i97 i94) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_959 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (¬ (formula_673 c2_level r3_depth r3_kind r3_node r3_sign)) := by
  exact (Or.elim (replay_943 c2_group c2_level r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim (l0 (replay_958 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i81 i95 i96 i97 i94)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i34 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_960 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (r3_kind ≥ (1 : Int)) := by
  exact (Or.elim (replay_942 c2_level r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim ((replay_959 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_961 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (¬ (r3_kind ≤ (0 : Int))) := by
  exact (Or.elim (replay_941 r3_kind) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_960 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94)))))

-- Checked replay of unit-resolution.
theorem replay_962 (c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (formula_671 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact (Or.elim (replay_940 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_961 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94) t0))))

theorem propositional_548 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_963 (r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_670 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (r3_kind ≥ (2 : Int))) := by
  exact (propositional_548 (r3_kind ≤ (2 : Int)) (r3_kind ≥ (2 : Int)) (r3_mode ≤ (0 : Int)) (r3_mode ≥ (0 : Int)) (r3_level ≤ (0 : Int)) (r3_level ≥ (0 : Int)) (r3_group ≤ (0 : Int)) (r3_group ≥ (0 : Int)) (r3_depth ≤ (0 : Int)) (r3_depth ≥ (0 : Int)) (r3_node ≤ (0 : Int)) (r3_node ≥ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_964 (r3_kind : Int) : ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_549 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_965 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : ((formula_673 c2_level r3_depth r3_kind r3_node r3_sign) ∨ (r3_kind ≤ (1 : Int))) := by
  exact (propositional_549 (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((r3_node % (2 : Int)) ≥ (1 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_966 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (r3_kind ≤ (1 : Int)) := by
  exact (Or.elim (replay_965 c2_level r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim ((replay_959 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_967 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (¬ (r3_kind ≥ (2 : Int))) := by
  exact (Or.elim (replay_964 r3_kind) (fun l0 => (False.elim (l0 (replay_966 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_968 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (formula_670 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact (Or.elim (replay_963 r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_967 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94) t0))))

-- Checked replay of unit-resolution.
theorem replay_969 (c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (¬ (formula_659 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  exact (Or.elim (replay_939 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93) (fun l0 => (False.elim (l0 (replay_968 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i34 i81 i95 i96 i97 i94)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_962 c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i34 i81 i95 i96 i97 i94)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_970 (c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (formula_647 h r3_depth r3_sign) := by
  exact (Or.elim (replay_927 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (fun l0 => (False.elim ((replay_969 c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93 i34 i81 i95 i96 i97 i94) l0))) (fun t0 => t0))

theorem propositional_550 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p7))))) ∨ (¬ ((((¬ p13) ∨ (¬ p10)) ∧ ((¬ ((¬ p14) ∨ (¬ p15))) ∨ (¬ ((¬ p16) ∨ (¬ p17))))) ∨ ((¬ ((¬ p13) ∨ (¬ p10))) ∧ (¬ ((¬ p18) ∨ (¬ p19))))))) ∨ p10) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_971 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_659 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) := by
  exact (propositional_550 (r3_mode ≤ (0 : Int)) (r3_mode ≥ (0 : Int)) (r3_level ≤ (0 : Int)) (r3_level ≥ (0 : Int)) (r3_group ≤ (0 : Int)) (r3_group ≥ (0 : Int)) (r3_depth ≥ (0 : Int)) (r3_node ≥ (0 : Int)) (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) (r3_depth ≤ (0 : Int)) (r3_node ≤ (0 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_972 (c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_971 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (fun l0 => (False.elim ((replay_969 c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93 i34 i81 i95 i96 i97 i94) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_973 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i82 : (formula_170 h r2_depth r2_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i39 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i90 : (formula_655 c0_level r3_depth r3_kind r3_sign)) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) := by
  exact (Or.elim (replay_926 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign) (fun l0 => (False.elim (l0 (replay_895 c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign i59 i82 i34 i39 i81)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_970 c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93 i34 i81 i95 i96 i97 i94)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i90))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_960 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_966 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_972 c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93 i34 i81 i95 i96 i97 i94)))) (fun t5 => (Or.elim t5 (fun l6 => l6) (fun t6 => (Or.elim t6 (fun l7 => (False.elim (l7 i76))) (fun t7 => (Or.elim t7 (fun l8 => (False.elim (l8 i86))) (fun t8 => (Or.elim t8 (fun l9 => (False.elim (l9 i85))) (fun t9 => (Or.elim t9 (fun l10 => (False.elim (i79 l10))) (fun t10 => (False.elim (t10 i80))))))))))))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_974 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i82 : (formula_170 h r2_depth r2_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i39 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i90 : (formula_655 c0_level r3_depth r3_kind r3_sign)) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_896 c1_level h r3_depth) (fun l0 => (False.elim (l0 i85))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_973 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93 i85 i59 i82 i34 i39 i86 i80 i79 i76 i81 i90 i95 i96 i97 i94)))) (fun t1 => t1))))

theorem propositional_551 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_975 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_188 c2_level r2_depth r2_kind r2_node r2_sign) ∨ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := by
  exact (propositional_551 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_976 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_975 c2_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim ((replay_890 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i81) l0))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_977 (c2_level r3_depth : Int) : ((¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_552 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p8) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_978 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : ((formula_673 c2_level r3_depth r3_kind r3_node r3_sign) ∨ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))) := by
  exact (propositional_552 (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((r3_node % (2 : Int)) ≥ (1 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_979 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_978 c2_level r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim ((replay_959 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_980 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) := by
  exact (Or.elim (replay_977 c2_level r3_depth) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_979 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94)))))

-- Checked replay of th-lemma.
theorem replay_981 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i82 : (formula_170 h r2_depth r2_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i39 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) (i90 : (formula_655 c0_level r3_depth r3_kind r3_sign)) (i95 : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) (i96 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i97 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) (i94 : (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) : False := by
  classical
  have k0 := (replay_887 c0_level r1_depth r2_depth i80 i79)
  have k1 := (replay_895 c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign i59 i82 i34 i39 i81)
  have k2 := (replay_974 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93 i85 i59 i82 i34 i39 i86 i80 i79 i76 i81 i90 i95 i96 i97 i94)
  have k3 := (replay_976 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i81)
  have k4 := (replay_980 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign i34 i81 i95 i96 i97 i94)
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair021_41 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ∨ (¬ ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ∨ (¬ (formula_655 c0_level r3_depth r3_kind r3_sign)) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∨ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (¬ (formula_170 h r2_depth r2_sign)) ∨ (¬ (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) ∨ (¬ ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_684 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_686 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))))
abbrev formula_689 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair021_41 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_982 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) : (formula_689 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_981 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i93 (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))

theorem propositional_553 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_983 (c2_group c2_level c2_mode r3_depth r3_kind r3_sign : Int) : (((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_677 c2_group c2_level r3_depth r3_kind r3_sign))) ∨ (c2_mode ≤ (0 : Int))) := by
  exact (propositional_553 (c2_mode ≤ (0 : Int)) (c2_mode ≥ (0 : Int)) (c2_group ≤ (1 : Int)) (c2_group ≥ (1 : Int)) (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_984 (c2_mode : Int) (i98 : (¬ (c2_mode ≥ (1 : Int)))) : (¬ (c2_mode ≥ (2 : Int))) := by
  exact (Or.elim (replay_218 c2_mode) (fun l0 => (False.elim (i98 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_985 (c2_mode : Int) (i98 : (¬ (c2_mode ≥ (1 : Int)))) : (¬ (c2_mode ≥ (3 : Int))) := by
  exact (Or.elim (replay_947 c2_mode) (fun l0 => (False.elim ((replay_984 c2_mode i98) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_986 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i98 : (¬ (c2_mode ≥ (1 : Int)))) : ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_948 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_985 c2_mode i98) t0))))

theorem propositional_554 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ ((¬ ((¬ p8) ∨ (¬ p9))) ∨ (¬ ((¬ p10) ∨ (¬ p11))))) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_987 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_187 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ∨ (c2_mode ≥ (2 : Int))) := by
  exact (propositional_554 (c2_mode ≤ (2 : Int)) (c2_mode ≥ (2 : Int)) (c2_group ≤ (1 : Int)) (c2_group ≥ (1 : Int)) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_988 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i98 : (¬ (c2_mode ≥ (1 : Int)))) : ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_187 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_987 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_984 c2_mode i98) t0))))

-- Checked replay of unit-resolution.
theorem replay_989 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i98 : (¬ (c2_mode ≥ (1 : Int)))) (i99 : ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign)))) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_182 c2_group c2_level r2_depth r2_kind r2_sign)))) := by
  exact (Or.elim (replay_215 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 i17))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i99))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_988 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i98)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_986 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i98)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i20))) (fun t5 => (False.elim (t5 i19))))))))))))))

end H4Formal.Generated.Repair
