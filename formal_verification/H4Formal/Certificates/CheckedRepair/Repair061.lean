import H4Formal.Certificates.CheckedRepair.Repair060

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair061_0 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))))) ∧ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))) ∨ (¬ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)))))
abbrev formula_1712 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_0 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)

theorem normalized_1458 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_1 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))))
abbrev shared_expr_Repair061_2 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair061_1 c2_depth c2_kind c2_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
theorem normalization_5807 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : (¬ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level)) := (not_congr (normalization_5802 c2_depth c2_kind c2_sign r0_group r0_level))

theorem normalization_5808 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))) ∨ (¬ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level))) ↔ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level))) := (or_congr (normalization_1834 r0_mode) (or_congr (normalization_1835 r0_mode) (normalization_5807 c2_depth c2_kind c2_sign r0_group r0_level)))

theorem normalization_5809 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))) ∨ (¬ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level)))) := (not_congr (normalization_5808 c2_depth c2_kind c2_sign r0_group r0_level r0_mode))

abbrev shared_expr_Repair061_3 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level)))))
theorem normalization_5810 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1712 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_3 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5805 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (normalization_5809 c2_depth c2_kind c2_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_3521 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1712 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1458 ((r0_mode) ≤ (1 : Int)) ((r0_mode) ≤ (0 : Int)) (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5810 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_4 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (1 : Int)) ∧ (formula_1682 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))) ∨ (¬ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)))))
abbrev formula_1713 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_4 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)

theorem normalized_1459 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_5 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair061_6 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair061_5 c2_depth c2_kind c2_sign r0_level)))
abbrev shared_expr_Repair061_7 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair061_6 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level)))))
theorem normalization_5811 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1713 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_7 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5663 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (normalization_5809 c2_depth c2_kind c2_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
abbrev shared_expr_Repair061_8 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair061_6 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level)))
theorem replay_3522 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1713 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1459 ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair061_6 c2_depth c2_kind c2_sign r0_group r0_level)) ((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair061_2 c2_depth c2_kind c2_sign r0_group r0_level))))
  have n0 : (shared_expr_Repair061_8 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5806 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (replay_3520 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)
  have n1 : (shared_expr_Repair061_3 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5810 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (replay_3521 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5811 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) hn

theorem normalized_1460 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5812 (c2_depth r0_level : Int) : (c2_depth ≤ r0_level) ↔ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5813 (c2_depth r0_level : Int) : (c2_depth ≥ r0_level) ↔ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5814 (c2_depth r0_level : Int) : ((c2_depth ≤ r0_level) ∧ (c2_depth ≥ r0_level)) ↔ (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (and_congr (normalization_5812 c2_depth r0_level) (normalization_5813 c2_depth r0_level))

abbrev shared_expr_Repair061_9 (c2_depth r0_level : Int) : Prop := ((((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ↔ (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))
theorem normalization_5815 (c2_depth r0_level : Int) : ((c2_depth = r0_level) ↔ ((c2_depth ≤ r0_level) ∧ (c2_depth ≥ r0_level))) ↔ (shared_expr_Repair061_9 c2_depth r0_level) := (iff_congr (normalization_5527 c2_depth r0_level) (normalization_5814 c2_depth r0_level))

-- Checked replay of rewrite.
theorem replay_3523 (c2_depth r0_level : Int) : ((c2_depth = r0_level) ↔ ((c2_depth ≤ r0_level) ∧ (c2_depth ≥ r0_level))) := by
  classical
  have ht := (normalized_1460 (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5815 c2_depth r0_level) hn

theorem normalized_1461 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5816 (c2_depth r0_level : Int) : ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5817 (c2_depth r0_level : Int) : ((c2_depth ≤ r0_level) ↔ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := (iff_congr (normalization_5812 c2_depth r0_level) (normalization_5816 c2_depth r0_level))

-- Checked replay of rewrite.
theorem replay_3524 (c2_depth r0_level : Int) : ((c2_depth ≤ r0_level) ↔ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1461 ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5817 c2_depth r0_level) hn

theorem normalized_1462 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5818 (c2_depth r0_level : Int) : ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5819 (c2_depth r0_level : Int) : ((c2_depth ≥ r0_level) ↔ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_5813 c2_depth r0_level) (normalization_5818 c2_depth r0_level))

-- Checked replay of rewrite.
theorem replay_3525 (c2_depth r0_level : Int) : ((c2_depth ≥ r0_level) ↔ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1462 ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5819 c2_depth r0_level) hn

theorem normalized_1463 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5820 (c2_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (and_congr (normalization_5816 c2_depth r0_level) (normalization_5818 c2_depth r0_level))

theorem normalization_5821 (c2_depth r0_level : Int) : (((c2_depth ≤ r0_level) ∧ (c2_depth ≥ r0_level)) ↔ (((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (shared_expr_Repair061_9 c2_depth r0_level) := (iff_congr (normalization_5814 c2_depth r0_level) (normalization_5820 c2_depth r0_level))

-- Checked replay of monotonicity.
theorem replay_3526 (c2_depth r0_level : Int) : (((c2_depth ≤ r0_level) ∧ (c2_depth ≥ r0_level)) ↔ (((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := by
  classical
  have ht := (normalized_1463 ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))
  have n0 : (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5817 c2_depth r0_level) (replay_3524 c2_depth r0_level)
  have n1 : ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5819 c2_depth r0_level) (replay_3525 c2_depth r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5821 c2_depth r0_level) hn

abbrev shared_expr_Repair061_10 (c2_depth r0_level : Int) : Prop := ((((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
abbrev formula_1714 (c2_depth r0_level : Int) : Prop := (shared_expr_Repair061_10 c2_depth r0_level)

theorem normalized_1464 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5822 (c2_depth r0_level : Int) : (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := (not_congr (normalization_5816 c2_depth r0_level))

theorem normalization_5823 (c2_depth r0_level : Int) : (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5818 c2_depth r0_level))

theorem normalization_5824 (c2_depth r0_level : Int) : ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) := (or_congr (normalization_5822 c2_depth r0_level) (normalization_5823 c2_depth r0_level))

theorem normalization_5825 (c2_depth r0_level : Int) : (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) := (not_congr (normalization_5824 c2_depth r0_level))

abbrev shared_expr_Repair061_11 (c2_depth r0_level : Int) : Prop := ((((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))))
theorem normalization_5826 (c2_depth r0_level : Int) : (formula_1714 c2_depth r0_level) ↔ (shared_expr_Repair061_11 c2_depth r0_level) := (iff_congr (normalization_5820 c2_depth r0_level) (normalization_5825 c2_depth r0_level))

-- Checked replay of rewrite.
theorem replay_3527 (c2_depth r0_level : Int) : (formula_1714 c2_depth r0_level) := by
  classical
  have ht := (normalized_1464 ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5826 c2_depth r0_level) hn

theorem normalized_1465 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5827 (c2_depth r0_level : Int) : (((c2_depth ≤ r0_level) ∧ (c2_depth ≥ r0_level)) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Repair061_11 c2_depth r0_level) := (iff_congr (normalization_5814 c2_depth r0_level) (normalization_5825 c2_depth r0_level))

-- Checked replay of trans.
theorem replay_3528 (c2_depth r0_level : Int) : (((c2_depth ≤ r0_level) ∧ (c2_depth ≥ r0_level)) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_1465 (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) (shared_expr_Repair061_11 c2_depth r0_level))
  have n0 : (shared_expr_Repair061_9 c2_depth r0_level) := by
    exact Iff.mp (normalization_5821 c2_depth r0_level) (replay_3526 c2_depth r0_level)
  have n1 : (shared_expr_Repair061_11 c2_depth r0_level) := by
    exact Iff.mp (normalization_5826 c2_depth r0_level) (replay_3527 c2_depth r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5827 c2_depth r0_level) hn

theorem normalized_1466 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5828 (c2_depth r0_level : Int) : ((c2_depth = r0_level) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Repair061_11 c2_depth r0_level) := (iff_congr (normalization_5527 c2_depth r0_level) (normalization_5825 c2_depth r0_level))

-- Checked replay of trans.
theorem replay_3529 (c2_depth r0_level : Int) : ((c2_depth = r0_level) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_1466 (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) (shared_expr_Repair061_11 c2_depth r0_level))
  have n0 : (shared_expr_Repair061_9 c2_depth r0_level) := by
    exact Iff.mp (normalization_5815 c2_depth r0_level) (replay_3523 c2_depth r0_level)
  have n1 : (shared_expr_Repair061_11 c2_depth r0_level) := by
    exact Iff.mp (normalization_5827 c2_depth r0_level) (replay_3528 c2_depth r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5828 c2_depth r0_level) hn

theorem normalized_1467 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5829 (c2_node : Int) : ((c2_node % (2 : Int)) ≥ (0 : Int)) ↔ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5830 (c2_node : Int) : (((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (and_congr (normalization_1089 c2_node) (normalization_5829 c2_node))

abbrev shared_expr_Repair061_12 (c2_node : Int) : Prop := (((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_5831 (c2_node : Int) : (((c2_node % (2 : Int)) = (0 : Int)) ↔ (((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (0 : Int)))) ↔ (shared_expr_Repair061_12 c2_node) := (iff_congr (normalization_819 c2_node) (normalization_5830 c2_node))

-- Checked replay of rewrite.
theorem replay_3530 (c2_node : Int) : (((c2_node % (2 : Int)) = (0 : Int)) ↔ (((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1467 ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5831 c2_node) hn

-- Checked replay of rewrite.
theorem replay_3531 (c2_node : Int) : (((c2_node % (2 : Int)) ≥ (0 : Int)) ↔ True) := by
  classical
  first | omega | grind (splits := 40)

theorem normalized_1468 (p0 p1 : Prop) : (((p0 ↔ True)) → (((¬ p1) ∧ p0) ↔ ((¬ p1) ∧ True))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5832 (c2_node : Int) : (((c2_node % (2 : Int)) ≥ (0 : Int)) ↔ True) ↔ (((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ True) := (iff_congr (normalization_5829 c2_node) (normalization_305))

theorem normalization_5833 (c2_node : Int) : (((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ True) := (and_congr (normalization_1089 c2_node) (normalization_305))

abbrev shared_expr_Repair061_13 (c2_node : Int) : Prop := (((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ True))
theorem normalization_5834 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (0 : Int))) ↔ (((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ True)) ↔ (shared_expr_Repair061_13 c2_node) := (iff_congr (normalization_5830 c2_node) (normalization_5833 c2_node))

-- Checked replay of monotonicity.
theorem replay_3532 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (0 : Int))) ↔ (((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ True)) := by
  classical
  have ht := (normalized_1468 ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : (((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ True) := by
    exact Iff.mp (normalization_5832 c2_node) (replay_3531 c2_node)
  have hn := ht n0
  exact Iff.mpr (normalization_5834 c2_node) hn

theorem normalized_1469 (p0 : Prop) : (((¬ p0) ∧ True) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5835 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((c2_node % (2 : Int)) ≤ (0 : Int))) ↔ (((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ True) ↔ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_5833 c2_node) (normalization_1089 c2_node))

-- Checked replay of rewrite.
theorem replay_3533 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((c2_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1469 ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5835 c2_node) hn

theorem normalized_1470 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_14 (c2_node : Int) : Prop := (((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5836 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (0 : Int))) ↔ ((c2_node % (2 : Int)) ≤ (0 : Int))) ↔ (shared_expr_Repair061_14 c2_node) := (iff_congr (normalization_5830 c2_node) (normalization_1089 c2_node))

-- Checked replay of trans.
theorem replay_3534 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (0 : Int))) ↔ ((c2_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1470 ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ True) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair061_13 c2_node) := by
    exact Iff.mp (normalization_5834 c2_node) (replay_3532 c2_node)
  have n1 : (((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ True) ↔ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5835 c2_node) (replay_3533 c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5836 c2_node) hn

theorem normalized_1471 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5837 (c2_node : Int) : (((c2_node % (2 : Int)) = (0 : Int)) ↔ ((c2_node % (2 : Int)) ≤ (0 : Int))) ↔ (shared_expr_Repair061_14 c2_node) := (iff_congr (normalization_819 c2_node) (normalization_1089 c2_node))

-- Checked replay of trans.
theorem replay_3535 (c2_node : Int) : (((c2_node % (2 : Int)) = (0 : Int)) ↔ ((c2_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1471 ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) (shared_expr_Repair061_14 c2_node))
  have n0 : (shared_expr_Repair061_12 c2_node) := by
    exact Iff.mp (normalization_5831 c2_node) (replay_3530 c2_node)
  have n1 : (shared_expr_Repair061_14 c2_node) := by
    exact Iff.mp (normalization_5836 c2_node) (replay_3534 c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5837 c2_node) hn

abbrev shared_expr_Repair061_15 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ∧ ((c2_node % (2 : Int)) ≤ (0 : Int)))
abbrev formula_1715 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := (shared_expr_Repair061_15 c2_depth c2_kind c2_node c2_sign r0_level)

theorem normalized_1472 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ (¬ p7))) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ (¬ p7)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_16 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ∧ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5838 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (formula_1715 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_16 c2_depth c2_kind c2_node c2_sign r0_level) := (and_congr (normalization_3071 c2_kind) (and_congr (normalization_5825 c2_depth r0_level) (and_congr (normalization_1067 c2_sign) (normalization_1089 c2_node))))

abbrev shared_expr_Repair061_17 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_5839 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int))) ↔ (formula_1715 c2_depth c2_kind c2_node c2_sign r0_level)) ↔ ((shared_expr_Repair061_17 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_16 c2_depth c2_kind c2_node c2_sign r0_level)) := (iff_congr (normalization_5599 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5838 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair061_18 (c2_sign : Int) : Prop := (((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
theorem replay_3536 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int))) ↔ (formula_1715 c2_depth c2_kind c2_node c2_sign r0_level)) := by
  classical
  have ht := (normalized_1472 (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3073 c2_kind) (replay_2154 c2_kind)
  have n1 : (shared_expr_Repair061_11 c2_depth r0_level) := by
    exact Iff.mp (normalization_5828 c2_depth r0_level) (replay_3529 c2_depth r0_level)
  have n2 : (shared_expr_Repair061_18 c2_sign) := by
    exact Iff.mp (normalization_5774 c2_sign) (replay_3503 c2_sign)
  have n3 : (shared_expr_Repair061_14 c2_node) := by
    exact Iff.mp (normalization_5837 c2_node) (replay_3535 c2_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_5839 c2_depth c2_kind c2_node c2_sign r0_level) hn

theorem normalized_1473 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ (¬ p5)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_19 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_5840 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (formula_1594 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1068 c2_sign) (or_congr (normalization_5822 c2_depth r0_level) (or_congr (normalization_5823 c2_depth r0_level) (normalization_1090 c2_node))))))

theorem normalization_5841 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (¬ (formula_1594 c2_depth c2_kind c2_node c2_sign r0_level)) ↔ (¬ (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level)) := (not_congr (normalization_5840 c2_depth c2_kind c2_node c2_sign r0_level))

theorem normalization_5842 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1715 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (formula_1594 c2_depth c2_kind c2_node c2_sign r0_level))) ↔ ((shared_expr_Repair061_16 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))) := (iff_congr (normalization_5838 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5841 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of rewrite.
theorem replay_3537 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1715 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (formula_1594 c2_depth c2_kind c2_node c2_sign r0_level))) := by
  classical
  have ht := (normalized_1473 ((c2_kind) ≤ (1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5842 c2_depth c2_kind c2_node c2_sign r0_level) hn

theorem normalized_1474 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_20 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int))) ↔ (¬ (formula_1594 c2_depth c2_kind c2_node c2_sign r0_level)))
theorem normalization_5843 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (shared_expr_Repair061_20 c2_depth c2_kind c2_node c2_sign r0_level) ↔ ((shared_expr_Repair061_17 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))) := (iff_congr (normalization_5599 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5841 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of trans.
theorem replay_3538 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (shared_expr_Repair061_20 c2_depth c2_kind c2_node c2_sign r0_level) := by
  classical
  have ht := (normalized_1474 (shared_expr_Repair061_17 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_16 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))
  have n0 : ((shared_expr_Repair061_17 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_16 c2_depth c2_kind c2_node c2_sign r0_level)) := by
    exact Iff.mp (normalization_5839 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3536 c2_depth c2_kind c2_node c2_sign r0_level)
  have n1 : ((shared_expr_Repair061_16 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))) := by
    exact Iff.mp (normalization_5842 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3537 c2_depth c2_kind c2_node c2_sign r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5843 c2_depth c2_kind c2_node c2_sign r0_level) hn

abbrev shared_expr_Repair061_21 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ (formula_1590 c2_depth c2_kind c2_sign r0_level))) ∨ ((¬ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ∧ (¬ (formula_1594 c2_depth c2_kind c2_node c2_sign r0_level))))
abbrev formula_1716 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (shared_expr_Repair061_21 c2_depth c2_kind c2_node c2_sign r0_group r0_level)

theorem normalized_1475 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_22 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))))
abbrev shared_expr_Repair061_23 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))))
theorem normalization_5844 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (formula_1716 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_23 c2_depth c2_kind c2_node c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1764 r0_group) (normalization_5778 c2_depth c2_kind c2_sign r0_level)) (and_congr (not_congr (normalization_1764 r0_group)) (normalization_5841 c2_depth c2_kind c2_node c2_sign r0_level)))

abbrev shared_expr_Repair061_24 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair061_25 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair061_24 c2_depth c2_kind c2_sign r0_level)) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair061_17 c2_depth c2_kind c2_node c2_sign r0_level)))
theorem normalization_5845 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1683 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1716 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_23 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5664 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5844 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of monotonicity.
theorem replay_3539 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1683 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1716 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1475 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (shared_expr_Repair061_24 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair061_17 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1766 r0_group) (replay_352 r0_group)
  have n1 : ((shared_expr_Repair061_24 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level))) := by
    exact Iff.mp (normalization_5780 c2_depth c2_kind c2_sign r0_level) (replay_3506 c2_depth c2_kind c2_sign r0_level)
  have n2 : ((shared_expr_Repair061_17 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))) := by
    exact Iff.mp (normalization_5843 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3538 c2_depth c2_kind c2_node c2_sign r0_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5845 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

theorem normalized_1476 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_26 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level))))
theorem normalization_5846 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1763 r0_group) (normalization_5841 c2_depth c2_kind c2_node c2_sign r0_level)) (and_congr (not_congr (normalization_1763 r0_group)) (normalization_5778 c2_depth c2_kind c2_sign r0_level)))

theorem normalization_5847 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1716 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_23 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5844 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5846 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of rewrite.
theorem replay_3540 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1716 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1476 ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair061_19 c2_depth c2_kind c2_node c2_sign r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5847 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

theorem normalized_1477 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5848 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1683 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5664 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5846 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of trans.
theorem replay_3541 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1683 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1477 (shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_23 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have n0 : ((shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_23 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5845 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3539 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have n1 : ((shared_expr_Repair061_23 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5847 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3540 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5848 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

abbrev shared_expr_Repair061_27 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (2 : Int)) ∧ (formula_1683 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int))))) ∧ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))
abbrev formula_1717 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_27 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1478 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5849 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : ((¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int))))) ∧ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (and_congr (normalization_1874 r0_mode) (normalization_5846 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

abbrev shared_expr_Repair061_28 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))
theorem normalization_5850 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1717 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_28 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5665 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5849 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_3542 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1717 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1478 (((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int))))) (shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have n0 : ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1876 r0_mode) (replay_387 r0_mode)
  have n1 : ((shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5848 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3541 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5850 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_29 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int))))) ∧ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int))) ∨ (¬ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
abbrev formula_1718 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_29 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1479 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5851 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (¬ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (not_congr (normalization_5846 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

theorem normalization_5852 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int))) ∨ (¬ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level))) ↔ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level))) := (or_congr (normalization_1871 r0_mode) (or_congr (normalization_1872 r0_mode) (normalization_5851 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))

theorem normalization_5853 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int))) ∨ (¬ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))) := (not_congr (normalization_5852 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

abbrev shared_expr_Repair061_30 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
theorem normalization_5854 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1718 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_30 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5849 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5853 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_3543 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1718 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1479 ((r0_mode) ≤ (2 : Int)) ((r0_mode) ≤ (1 : Int)) (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5854 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_31 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (2 : Int)) ∧ (formula_1683 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int))) ∨ (¬ (formula_1595 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
abbrev formula_1719 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_31 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1480 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_32 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
theorem normalization_5855 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1719 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_32 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5665 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5853 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_3544 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1719 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1480 ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair061_25 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ((¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair061_26 c2_depth c2_kind c2_node c2_sign r0_group r0_level))))
  have n0 : (shared_expr_Repair061_28 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5850 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (replay_3542 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)
  have n1 : (shared_expr_Repair061_30 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5854 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (replay_3543 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5855 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

theorem normalized_1481 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5856 (c2_node : Int) : ((c2_node % (2 : Int)) ≤ (1 : Int)) ↔ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) := by
  omega

theorem normalization_5857 (c2_node : Int) : (((c2_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := (and_congr (normalization_5856 c2_node) (normalization_1101 c2_node))

abbrev shared_expr_Repair061_33 (c2_node : Int) : Prop := (((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5858 (c2_node : Int) : (((c2_node % (2 : Int)) = (1 : Int)) ↔ (((c2_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int)))) ↔ (shared_expr_Repair061_33 c2_node) := (iff_congr (normalization_823 c2_node) (normalization_5857 c2_node))

-- Checked replay of rewrite.
theorem replay_3545 (c2_node : Int) : (((c2_node % (2 : Int)) = (1 : Int)) ↔ (((c2_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1481 ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5858 c2_node) hn

-- Checked replay of rewrite.
theorem replay_3546 (c2_node : Int) : (((c2_node % (2 : Int)) ≤ (1 : Int)) ↔ True) := by
  classical
  first | omega | grind (splits := 40)

theorem normalized_1482 (p0 p1 : Prop) : ((((¬ p0) ↔ True)) → (((¬ p0) ∧ p1) ↔ (True ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5859 (c2_node : Int) : (((c2_node % (2 : Int)) ≤ (1 : Int)) ↔ True) ↔ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ↔ True) := (iff_congr (normalization_5856 c2_node) (normalization_305))

theorem normalization_5860 (c2_node : Int) : (True ∧ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := (and_congr (normalization_305) (normalization_1101 c2_node))

abbrev shared_expr_Repair061_34 (c2_node : Int) : Prop := (((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ (True ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5861 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((c2_node % (2 : Int)) ≥ (1 : Int)))) ↔ (shared_expr_Repair061_34 c2_node) := (iff_congr (normalization_5857 c2_node) (normalization_5860 c2_node))

-- Checked replay of monotonicity.
theorem replay_3547 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((c2_node % (2 : Int)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1482 ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int)) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ↔ True) := by
    exact Iff.mp (normalization_5859 c2_node) (replay_3546 c2_node)
  have hn := ht n0
  exact Iff.mpr (normalization_5861 c2_node) hn

theorem normalized_1483 (p0 : Prop) : ((True ∧ p0) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5862 (c2_node : Int) : ((True ∧ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ ((True ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := (iff_congr (normalization_5860 c2_node) (normalization_1101 c2_node))

-- Checked replay of rewrite.
theorem replay_3548 (c2_node : Int) : ((True ∧ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c2_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_1483 ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5862 c2_node) hn

theorem normalized_1484 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_35 (c2_node : Int) : Prop := (((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
theorem normalization_5863 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ (shared_expr_Repair061_35 c2_node) := (iff_congr (normalization_5857 c2_node) (normalization_1101 c2_node))

-- Checked replay of trans.
theorem replay_3549 (c2_node : Int) : ((((c2_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c2_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_1484 ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) (True ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair061_34 c2_node) := by
    exact Iff.mp (normalization_5861 c2_node) (replay_3547 c2_node)
  have n1 : ((True ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
    exact Iff.mp (normalization_5862 c2_node) (replay_3548 c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5863 c2_node) hn

theorem normalized_1485 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5864 (c2_node : Int) : (((c2_node % (2 : Int)) = (1 : Int)) ↔ ((c2_node % (2 : Int)) ≥ (1 : Int))) ↔ (shared_expr_Repair061_35 c2_node) := (iff_congr (normalization_823 c2_node) (normalization_1101 c2_node))

-- Checked replay of trans.
theorem replay_3550 (c2_node : Int) : (((c2_node % (2 : Int)) = (1 : Int)) ↔ ((c2_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_1485 ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) (shared_expr_Repair061_35 c2_node))
  have n0 : (shared_expr_Repair061_33 c2_node) := by
    exact Iff.mp (normalization_5858 c2_node) (replay_3545 c2_node)
  have n1 : (shared_expr_Repair061_35 c2_node) := by
    exact Iff.mp (normalization_5863 c2_node) (replay_3549 c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5864 c2_node) hn

abbrev shared_expr_Repair061_36 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int)))
abbrev formula_1720 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := (shared_expr_Repair061_36 c2_depth c2_kind c2_node c2_sign r0_level)

theorem normalized_1486 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ p7)) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ p7))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_37 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
theorem normalization_5865 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (formula_1720 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_37 c2_depth c2_kind c2_node c2_sign r0_level) := (and_congr (normalization_3071 c2_kind) (and_congr (normalization_5825 c2_depth r0_level) (and_congr (normalization_1067 c2_sign) (normalization_1101 c2_node))))

abbrev shared_expr_Repair061_38 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5866 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int))) ↔ (formula_1720 c2_depth c2_kind c2_node c2_sign r0_level)) ↔ ((shared_expr_Repair061_38 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_37 c2_depth c2_kind c2_node c2_sign r0_level)) := (iff_congr (normalization_5602 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5865 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of monotonicity.
theorem replay_3551 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int))) ↔ (formula_1720 c2_depth c2_kind c2_node c2_sign r0_level)) := by
  classical
  have ht := (normalized_1486 (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3073 c2_kind) (replay_2154 c2_kind)
  have n1 : (shared_expr_Repair061_11 c2_depth r0_level) := by
    exact Iff.mp (normalization_5828 c2_depth r0_level) (replay_3529 c2_depth r0_level)
  have n2 : (shared_expr_Repair061_18 c2_sign) := by
    exact Iff.mp (normalization_5774 c2_sign) (replay_3503 c2_sign)
  have n3 : (shared_expr_Repair061_35 c2_node) := by
    exact Iff.mp (normalization_5864 c2_node) (replay_3550 c2_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_5866 c2_depth c2_kind c2_node c2_sign r0_level) hn

theorem normalized_1487 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ p5) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_39 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5867 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (formula_1596 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1068 c2_sign) (or_congr (normalization_5822 c2_depth r0_level) (or_congr (normalization_5823 c2_depth r0_level) (normalization_1102 c2_node))))))

theorem normalization_5868 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (¬ (formula_1596 c2_depth c2_kind c2_node c2_sign r0_level)) ↔ (¬ (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level)) := (not_congr (normalization_5867 c2_depth c2_kind c2_node c2_sign r0_level))

theorem normalization_5869 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1720 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (formula_1596 c2_depth c2_kind c2_node c2_sign r0_level))) ↔ ((shared_expr_Repair061_37 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))) := (iff_congr (normalization_5865 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5868 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of rewrite.
theorem replay_3552 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1720 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (formula_1596 c2_depth c2_kind c2_node c2_sign r0_level))) := by
  classical
  have ht := (normalized_1487 ((c2_kind) ≤ (1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5869 c2_depth c2_kind c2_node c2_sign r0_level) hn

theorem normalized_1488 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_40 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int))) ↔ (¬ (formula_1596 c2_depth c2_kind c2_node c2_sign r0_level)))
theorem normalization_5870 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (shared_expr_Repair061_40 c2_depth c2_kind c2_node c2_sign r0_level) ↔ ((shared_expr_Repair061_38 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))) := (iff_congr (normalization_5602 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5868 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of trans.
theorem replay_3553 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (shared_expr_Repair061_40 c2_depth c2_kind c2_node c2_sign r0_level) := by
  classical
  have ht := (normalized_1488 (shared_expr_Repair061_38 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_37 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))
  have n0 : ((shared_expr_Repair061_38 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_37 c2_depth c2_kind c2_node c2_sign r0_level)) := by
    exact Iff.mp (normalization_5866 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3551 c2_depth c2_kind c2_node c2_sign r0_level)
  have n1 : ((shared_expr_Repair061_37 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))) := by
    exact Iff.mp (normalization_5869 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3552 c2_depth c2_kind c2_node c2_sign r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5870 c2_depth c2_kind c2_node c2_sign r0_level) hn

abbrev shared_expr_Repair061_41 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ (formula_1590 c2_depth c2_kind c2_sign r0_level))) ∨ ((¬ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ∧ (¬ (formula_1596 c2_depth c2_kind c2_node c2_sign r0_level))))
abbrev formula_1721 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (shared_expr_Repair061_41 c2_depth c2_kind c2_node c2_sign r0_group r0_level)

theorem normalized_1489 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_42 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))))
theorem normalization_5871 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (formula_1721 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_42 c2_depth c2_kind c2_node c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1764 r0_group) (normalization_5778 c2_depth c2_kind c2_sign r0_level)) (and_congr (not_congr (normalization_1764 r0_group)) (normalization_5868 c2_depth c2_kind c2_node c2_sign r0_level)))

abbrev shared_expr_Repair061_43 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair061_24 c2_depth c2_kind c2_sign r0_level)) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair061_38 c2_depth c2_kind c2_node c2_sign r0_level)))
theorem normalization_5872 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1684 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1721 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_42 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5666 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5871 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of monotonicity.
theorem replay_3554 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1684 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1721 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1489 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (shared_expr_Repair061_24 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair061_38 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1766 r0_group) (replay_352 r0_group)
  have n1 : ((shared_expr_Repair061_24 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level))) := by
    exact Iff.mp (normalization_5780 c2_depth c2_kind c2_sign r0_level) (replay_3506 c2_depth c2_kind c2_sign r0_level)
  have n2 : ((shared_expr_Repair061_38 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))) := by
    exact Iff.mp (normalization_5870 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3553 c2_depth c2_kind c2_node c2_sign r0_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5872 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

theorem normalized_1490 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_44 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level))))
theorem normalization_5873 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1763 r0_group) (normalization_5868 c2_depth c2_kind c2_node c2_sign r0_level)) (and_congr (not_congr (normalization_1763 r0_group)) (normalization_5778 c2_depth c2_kind c2_sign r0_level)))

theorem normalization_5874 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1721 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_42 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5871 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5873 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of rewrite.
theorem replay_3555 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1721 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1490 ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (shared_expr_Repair061_22 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair061_39 c2_depth c2_kind c2_node c2_sign r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5874 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

theorem normalized_1491 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5875 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1684 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5666 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5873 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of trans.
theorem replay_3556 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1684 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1491 (shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_42 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have n0 : ((shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_42 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5872 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3554 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have n1 : ((shared_expr_Repair061_42 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5874 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3555 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5875 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

abbrev shared_expr_Repair061_45 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (3 : Int)) ∧ (formula_1684 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ (r0_mode ≤ (3 : Int))) ∨ (¬ (r0_mode ≥ (3 : Int))))) ∧ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))
abbrev formula_1722 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_45 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1492 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5876 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : ((¬ ((¬ (r0_mode ≤ (3 : Int))) ∨ (¬ (r0_mode ≥ (3 : Int))))) ∧ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (and_congr (normalization_1930 r0_mode) (normalization_5873 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

abbrev shared_expr_Repair061_46 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (3 : Int)) ∧ (¬ ((r0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))
theorem normalization_5877 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1722 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_46 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5667 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5876 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_3557 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1722 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1492 (((r0_mode) ≤ (3 : Int)) ∧ (¬ ((r0_mode) ≤ (2 : Int)))) ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int))))) (shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have n0 : ((((r0_mode) ≤ (3 : Int)) ∧ (¬ ((r0_mode) ≤ (2 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int))))))) := by
    exact Iff.mp (normalization_1932 r0_mode) (replay_412 r0_mode)
  have n1 : ((shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5875 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3556 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5877 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_47 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (r0_mode ≤ (3 : Int))) ∨ (¬ (r0_mode ≥ (3 : Int))))) ∧ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (3 : Int))) ∨ (¬ (r0_mode ≥ (3 : Int))) ∨ (¬ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
abbrev formula_1723 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_47 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1493 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5878 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (¬ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (not_congr (normalization_5873 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

theorem normalization_5879 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : ((¬ (r0_mode ≤ (3 : Int))) ∨ (¬ (r0_mode ≥ (3 : Int))) ∨ (¬ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level))) ↔ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level))) := (or_congr (normalization_1927 r0_mode) (or_congr (normalization_1928 r0_mode) (normalization_5878 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))

theorem normalization_5880 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (3 : Int))) ∨ (¬ (r0_mode ≥ (3 : Int))) ∨ (¬ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))) ↔ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))) := (not_congr (normalization_5879 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

abbrev shared_expr_Repair061_48 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
theorem normalization_5881 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1723 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_48 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5876 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5880 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_3558 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1723 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1493 ((r0_mode) ≤ (3 : Int)) ((r0_mode) ≤ (2 : Int)) (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5881 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_49 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (3 : Int)) ∧ (formula_1684 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (3 : Int))) ∨ (¬ (r0_mode ≥ (3 : Int))) ∨ (¬ (formula_1597 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
abbrev formula_1724 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_49 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1494 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_50 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (3 : Int)) ∧ (¬ ((r0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
theorem normalization_5882 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1724 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_50 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5667 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5880 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_3559 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1724 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1494 ((((r0_mode) ≤ (3 : Int)) ∧ (¬ ((r0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair061_43 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair061_44 c2_depth c2_kind c2_node c2_sign r0_group r0_level))))
  have n0 : (shared_expr_Repair061_46 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5877 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (replay_3557 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)
  have n1 : (shared_expr_Repair061_48 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5881 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (replay_3558 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5882 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_51 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ∧ ((c2_node % (2 : Int)) ≤ (0 : Int)))
abbrev formula_1725 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := (shared_expr_Repair061_51 c2_depth c2_kind c2_node c2_sign r0_level)

theorem normalized_1495 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ (¬ p7))) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ (¬ p7)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_52 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ∧ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5883 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (formula_1725 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_52 c2_depth c2_kind c2_node c2_sign r0_level) := (and_congr (normalization_3071 c2_kind) (and_congr (normalization_5825 c2_depth r0_level) (and_congr (normalization_1081 c2_sign) (normalization_1089 c2_node))))

abbrev shared_expr_Repair061_53 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_5884 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int))) ↔ (formula_1725 c2_depth c2_kind c2_node c2_sign r0_level)) ↔ ((shared_expr_Repair061_53 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_52 c2_depth c2_kind c2_node c2_sign r0_level)) := (iff_congr (normalization_5605 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5883 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair061_54 (c2_sign : Int) : Prop := (((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
theorem replay_3560 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int))) ↔ (formula_1725 c2_depth c2_kind c2_node c2_sign r0_level)) := by
  classical
  have ht := (normalized_1495 (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3073 c2_kind) (replay_2154 c2_kind)
  have n1 : (shared_expr_Repair061_11 c2_depth r0_level) := by
    exact Iff.mp (normalization_5828 c2_depth r0_level) (replay_3529 c2_depth r0_level)
  have n2 : (shared_expr_Repair061_54 c2_sign) := by
    exact Iff.mp (normalization_5793 c2_sign) (replay_3513 c2_sign)
  have n3 : (shared_expr_Repair061_14 c2_node) := by
    exact Iff.mp (normalization_5837 c2_node) (replay_3535 c2_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_5884 c2_depth c2_kind c2_node c2_sign r0_level) hn

theorem normalized_1496 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ (¬ p5)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_55 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_5885 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (formula_1598 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1082 c2_sign) (or_congr (normalization_5822 c2_depth r0_level) (or_congr (normalization_5823 c2_depth r0_level) (normalization_1090 c2_node))))))

theorem normalization_5886 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (¬ (formula_1598 c2_depth c2_kind c2_node c2_sign r0_level)) ↔ (¬ (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level)) := (not_congr (normalization_5885 c2_depth c2_kind c2_node c2_sign r0_level))

theorem normalization_5887 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1725 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (formula_1598 c2_depth c2_kind c2_node c2_sign r0_level))) ↔ ((shared_expr_Repair061_52 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level))) := (iff_congr (normalization_5883 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5886 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of rewrite.
theorem replay_3561 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1725 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (formula_1598 c2_depth c2_kind c2_node c2_sign r0_level))) := by
  classical
  have ht := (normalized_1496 ((c2_kind) ≤ (1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5887 c2_depth c2_kind c2_node c2_sign r0_level) hn

theorem normalized_1497 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_56 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int))) ↔ (¬ (formula_1598 c2_depth c2_kind c2_node c2_sign r0_level)))
theorem normalization_5888 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (shared_expr_Repair061_56 c2_depth c2_kind c2_node c2_sign r0_level) ↔ ((shared_expr_Repair061_53 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level))) := (iff_congr (normalization_5605 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5886 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of trans.
theorem replay_3562 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (shared_expr_Repair061_56 c2_depth c2_kind c2_node c2_sign r0_level) := by
  classical
  have ht := (normalized_1497 (shared_expr_Repair061_53 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_52 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level))
  have n0 : ((shared_expr_Repair061_53 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_52 c2_depth c2_kind c2_node c2_sign r0_level)) := by
    exact Iff.mp (normalization_5884 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3560 c2_depth c2_kind c2_node c2_sign r0_level)
  have n1 : ((shared_expr_Repair061_52 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level))) := by
    exact Iff.mp (normalization_5887 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3561 c2_depth c2_kind c2_node c2_sign r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5888 c2_depth c2_kind c2_node c2_sign r0_level) hn

abbrev shared_expr_Repair061_57 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ (formula_1598 c2_depth c2_kind c2_node c2_sign r0_level))) ∨ ((¬ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ∧ (¬ (formula_1592 c2_depth c2_kind c2_sign r0_level))))
abbrev formula_1726 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (shared_expr_Repair061_57 c2_depth c2_kind c2_node c2_sign r0_group r0_level)

theorem normalized_1498 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_58 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair061_1 c2_depth c2_kind c2_sign r0_level))))
theorem normalization_5889 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (formula_1726 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_58 c2_depth c2_kind c2_node c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1764 r0_group) (normalization_5886 c2_depth c2_kind c2_node c2_sign r0_level)) (and_congr (not_congr (normalization_1764 r0_group)) (normalization_5797 c2_depth c2_kind c2_sign r0_level)))

abbrev shared_expr_Repair061_59 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair061_53 c2_depth c2_kind c2_node c2_sign r0_level)) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair061_5 c2_depth c2_kind c2_sign r0_level)))
theorem normalization_5890 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1685 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1726 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_58 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5668 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5889 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of monotonicity.
theorem replay_3563 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1685 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1726 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1498 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (shared_expr_Repair061_53 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_5 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair061_1 c2_depth c2_kind c2_sign r0_level))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1766 r0_group) (replay_352 r0_group)
  have n1 : ((shared_expr_Repair061_53 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level))) := by
    exact Iff.mp (normalization_5888 c2_depth c2_kind c2_node c2_sign r0_level) (replay_3562 c2_depth c2_kind c2_node c2_sign r0_level)
  have n2 : ((shared_expr_Repair061_5 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_1 c2_depth c2_kind c2_sign r0_level))) := by
    exact Iff.mp (normalization_5799 c2_depth c2_kind c2_sign r0_level) (replay_3516 c2_depth c2_kind c2_sign r0_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5890 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

theorem normalized_1499 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_60 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair061_1 c2_depth c2_kind c2_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level))))
theorem normalization_5891 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1763 r0_group) (normalization_5797 c2_depth c2_kind c2_sign r0_level)) (and_congr (not_congr (normalization_1763 r0_group)) (normalization_5886 c2_depth c2_kind c2_node c2_sign r0_level)))

theorem normalization_5892 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1726 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_58 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5889 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5891 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of rewrite.
theorem replay_3564 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1726 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1499 ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (shared_expr_Repair061_55 c2_depth c2_kind c2_node c2_sign r0_level) (shared_expr_Repair061_1 c2_depth c2_kind c2_sign r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5892 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

theorem normalized_1500 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5893 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1685 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (iff_congr (normalization_5668 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (normalization_5891 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

-- Checked replay of trans.
theorem replay_3565 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((formula_1685 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1500 (shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_58 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have n0 : ((shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_58 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5890 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3563 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have n1 : ((shared_expr_Repair061_58 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5892 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3564 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5893 c2_depth c2_kind c2_node c2_sign r0_group r0_level) hn

abbrev shared_expr_Repair061_61 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (4 : Int)) ∧ (formula_1685 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))))) ∧ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))
abbrev formula_1727 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_61 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1501 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5894 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : ((¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))))) ∧ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (and_congr (normalization_1969 r0_mode) (normalization_5891 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

abbrev shared_expr_Repair061_62 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))
theorem normalization_5895 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1727 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_62 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5669 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5894 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_3566 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1727 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1501 (((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int))))) (shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have n0 : ((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int))))))) := by
    exact Iff.mp (normalization_1971 r0_mode) (replay_430 r0_mode)
  have n1 : ((shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level) ↔ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5893 c2_depth c2_kind c2_node c2_sign r0_group r0_level) (replay_3565 c2_depth c2_kind c2_node c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5895 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_63 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))))) ∧ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))) ∨ (¬ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
abbrev formula_1728 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_63 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1502 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5896 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : (¬ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := (not_congr (normalization_5891 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

theorem normalization_5897 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))) ∨ (¬ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level))) ↔ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level))) := (or_congr (normalization_1966 r0_mode) (or_congr (normalization_1967 r0_mode) (normalization_5896 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))

theorem normalization_5898 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))) ∨ (¬ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))) ↔ (¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))) := (not_congr (normalization_5897 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

abbrev shared_expr_Repair061_64 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
theorem normalization_5899 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1728 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_64 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5894 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5898 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_3567 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1728 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1502 ((r0_mode) ≤ (4 : Int)) ((r0_mode) ≤ (3 : Int)) (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5899 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_65 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (4 : Int)) ∧ (formula_1685 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))) ∨ (¬ (formula_1599 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
abbrev formula_1729 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair061_65 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)

theorem normalized_1503 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_66 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)))))
theorem normalization_5900 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1729 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair061_66 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5669 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (normalization_5898 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_3568 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (formula_1729 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1503 ((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair061_59 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair061_60 c2_depth c2_kind c2_node c2_sign r0_group r0_level))))
  have n0 : (shared_expr_Repair061_62 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5895 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (replay_3566 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)
  have n1 : (shared_expr_Repair061_64 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5899 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) (replay_3567 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5900 c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair061_67 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ∧ ((c2_node % (2 : Int)) ≥ (1 : Int)))
abbrev formula_1730 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := (shared_expr_Repair061_67 c2_depth c2_kind c2_node c2_sign r0_level)

theorem normalized_1504 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ p7)) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ p7))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_68 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
theorem normalization_5901 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (formula_1730 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_68 c2_depth c2_kind c2_node c2_sign r0_level) := (and_congr (normalization_3071 c2_kind) (and_congr (normalization_5825 c2_depth r0_level) (and_congr (normalization_1081 c2_sign) (normalization_1101 c2_node))))

abbrev shared_expr_Repair061_69 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5902 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int))) ↔ (formula_1730 c2_depth c2_kind c2_node c2_sign r0_level)) ↔ ((shared_expr_Repair061_69 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_68 c2_depth c2_kind c2_node c2_sign r0_level)) := (iff_congr (normalization_5608 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5901 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of monotonicity.
theorem replay_3569 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ (c2_depth = r0_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int))) ↔ (formula_1730 c2_depth c2_kind c2_node c2_sign r0_level)) := by
  classical
  have ht := (normalized_1504 (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) (((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3073 c2_kind) (replay_2154 c2_kind)
  have n1 : (shared_expr_Repair061_11 c2_depth r0_level) := by
    exact Iff.mp (normalization_5828 c2_depth r0_level) (replay_3529 c2_depth r0_level)
  have n2 : (shared_expr_Repair061_54 c2_sign) := by
    exact Iff.mp (normalization_5793 c2_sign) (replay_3513 c2_sign)
  have n3 : (shared_expr_Repair061_35 c2_node) := by
    exact Iff.mp (normalization_5864 c2_node) (replay_3550 c2_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_5902 c2_depth c2_kind c2_node c2_sign r0_level) hn

theorem normalized_1505 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ p5) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair061_70 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_5903 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (formula_1600 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (shared_expr_Repair061_70 c2_depth c2_kind c2_node c2_sign r0_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1082 c2_sign) (or_congr (normalization_5822 c2_depth r0_level) (or_congr (normalization_5823 c2_depth r0_level) (normalization_1102 c2_node))))))

theorem normalization_5904 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : (¬ (formula_1600 c2_depth c2_kind c2_node c2_sign r0_level)) ↔ (¬ (shared_expr_Repair061_70 c2_depth c2_kind c2_node c2_sign r0_level)) := (not_congr (normalization_5903 c2_depth c2_kind c2_node c2_sign r0_level))

theorem normalization_5905 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1730 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (formula_1600 c2_depth c2_kind c2_node c2_sign r0_level))) ↔ ((shared_expr_Repair061_68 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (shared_expr_Repair061_70 c2_depth c2_kind c2_node c2_sign r0_level))) := (iff_congr (normalization_5901 c2_depth c2_kind c2_node c2_sign r0_level) (normalization_5904 c2_depth c2_kind c2_node c2_sign r0_level))

-- Checked replay of rewrite.
theorem replay_3570 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1730 c2_depth c2_kind c2_node c2_sign r0_level) ↔ (¬ (formula_1600 c2_depth c2_kind c2_node c2_sign r0_level))) := by
  classical
  have ht := (normalized_1505 ((c2_kind) ≤ (1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5905 c2_depth c2_kind c2_node c2_sign r0_level) hn

end H4Formal.Generated.Repair
