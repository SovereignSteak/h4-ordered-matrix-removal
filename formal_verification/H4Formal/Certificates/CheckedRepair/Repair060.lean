import H4Formal.Certificates.CheckedRepair.Repair059

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_3472 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i210 : ((formula_1654 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) : (formula_1696 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  exact Iff.mp (replay_3471 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_3470 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i210)

theorem normalized_1410 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5703 (c2_mode r0_mode : Int) : (r0_mode ≤ c2_mode) ↔ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5704 (c2_mode r0_mode : Int) : (r0_mode ≥ c2_mode) ↔ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_5705 (c2_mode r0_mode : Int) : ((r0_mode ≤ c2_mode) ∧ (r0_mode ≥ c2_mode)) ↔ ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) := (and_congr (normalization_5703 c2_mode r0_mode) (normalization_5704 c2_mode r0_mode))

abbrev shared_expr_Repair060_0 (c2_mode r0_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))))
theorem normalization_5706 (c2_mode r0_mode : Int) : ((r0_mode = c2_mode) ↔ ((r0_mode ≤ c2_mode) ∧ (r0_mode ≥ c2_mode))) ↔ (shared_expr_Repair060_0 c2_mode r0_mode) := (iff_congr (normalization_5516 c2_mode r0_mode) (normalization_5705 c2_mode r0_mode))

-- Checked replay of rewrite.
theorem replay_3473 (c2_mode r0_mode : Int) : ((r0_mode = c2_mode) ↔ ((r0_mode ≤ c2_mode) ∧ (r0_mode ≥ c2_mode))) := by
  classical
  have ht := (normalized_1410 ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5706 c2_mode r0_mode) hn

theorem normalized_1411 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5707 (c2_mode r0_mode : Int) : ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ↔ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5708 (c2_mode r0_mode : Int) : ((r0_mode ≤ c2_mode) ↔ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_5703 c2_mode r0_mode) (normalization_5707 c2_mode r0_mode))

-- Checked replay of rewrite.
theorem replay_3474 (c2_mode r0_mode : Int) : ((r0_mode ≤ c2_mode) ↔ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1411 ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5708 c2_mode r0_mode) hn

theorem normalized_1412 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5709 (c2_mode r0_mode : Int) : ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_5710 (c2_mode r0_mode : Int) : ((r0_mode ≥ c2_mode) ↔ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) := (iff_congr (normalization_5704 c2_mode r0_mode) (normalization_5709 c2_mode r0_mode))

-- Checked replay of rewrite.
theorem replay_3475 (c2_mode r0_mode : Int) : ((r0_mode ≥ c2_mode) ↔ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1412 ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5710 c2_mode r0_mode) hn

theorem normalized_1413 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5711 (c2_mode r0_mode : Int) : (((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) := (and_congr (normalization_5707 c2_mode r0_mode) (normalization_5709 c2_mode r0_mode))

theorem normalization_5712 (c2_mode r0_mode : Int) : (((r0_mode ≤ c2_mode) ∧ (r0_mode ≥ c2_mode)) ↔ (((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Repair060_0 c2_mode r0_mode) := (iff_congr (normalization_5705 c2_mode r0_mode) (normalization_5711 c2_mode r0_mode))

-- Checked replay of monotonicity.
theorem replay_3476 (c2_mode r0_mode : Int) : (((r0_mode ≤ c2_mode) ∧ (r0_mode ≥ c2_mode)) ↔ (((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1413 ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5708 c2_mode r0_mode) (replay_3474 c2_mode r0_mode)
  have n1 : (((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5710 c2_mode r0_mode) (replay_3475 c2_mode r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5712 c2_mode r0_mode) hn

abbrev shared_expr_Repair060_1 (c2_mode r0_mode : Int) : Prop := ((((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))))
abbrev formula_1698 (c2_mode r0_mode : Int) : Prop := (shared_expr_Repair060_1 c2_mode r0_mode)

theorem normalized_1414 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5713 (c2_mode r0_mode : Int) : (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_5707 c2_mode r0_mode))

theorem normalization_5714 (c2_mode r0_mode : Int) : (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) := (not_congr (normalization_5709 c2_mode r0_mode))

theorem normalization_5715 (c2_mode r0_mode : Int) : ((¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)))) := (or_congr (normalization_5713 c2_mode r0_mode) (normalization_5714 c2_mode r0_mode))

theorem normalization_5716 (c2_mode r0_mode : Int) : (¬ ((¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))))) := (not_congr (normalization_5715 c2_mode r0_mode))

abbrev shared_expr_Repair060_2 (c2_mode r0_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))))))
theorem normalization_5717 (c2_mode r0_mode : Int) : (formula_1698 c2_mode r0_mode) ↔ (shared_expr_Repair060_2 c2_mode r0_mode) := (iff_congr (normalization_5711 c2_mode r0_mode) (normalization_5716 c2_mode r0_mode))

-- Checked replay of rewrite.
theorem replay_3477 (c2_mode r0_mode : Int) : (formula_1698 c2_mode r0_mode) := by
  classical
  have ht := (normalized_1414 ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5717 c2_mode r0_mode) hn

theorem normalized_1415 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5718 (c2_mode r0_mode : Int) : (((r0_mode ≤ c2_mode) ∧ (r0_mode ≥ c2_mode)) ↔ (¬ ((¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair060_2 c2_mode r0_mode) := (iff_congr (normalization_5705 c2_mode r0_mode) (normalization_5716 c2_mode r0_mode))

-- Checked replay of trans.
theorem replay_3478 (c2_mode r0_mode : Int) : (((r0_mode ≤ c2_mode) ∧ (r0_mode ≥ c2_mode)) ↔ (¬ ((¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1415 ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) (shared_expr_Repair060_2 c2_mode r0_mode))
  have n0 : (shared_expr_Repair060_0 c2_mode r0_mode) := by
    exact Iff.mp (normalization_5712 c2_mode r0_mode) (replay_3476 c2_mode r0_mode)
  have n1 : (shared_expr_Repair060_2 c2_mode r0_mode) := by
    exact Iff.mp (normalization_5717 c2_mode r0_mode) (replay_3477 c2_mode r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5718 c2_mode r0_mode) hn

theorem normalized_1416 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5719 (c2_mode r0_mode : Int) : ((r0_mode = c2_mode) ↔ (¬ ((¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair060_2 c2_mode r0_mode) := (iff_congr (normalization_5516 c2_mode r0_mode) (normalization_5716 c2_mode r0_mode))

-- Checked replay of trans.
theorem replay_3479 (c2_mode r0_mode : Int) : ((r0_mode = c2_mode) ↔ (¬ ((¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1416 ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) (shared_expr_Repair060_2 c2_mode r0_mode))
  have n0 : (shared_expr_Repair060_0 c2_mode r0_mode) := by
    exact Iff.mp (normalization_5706 c2_mode r0_mode) (replay_3473 c2_mode r0_mode)
  have n1 : (shared_expr_Repair060_2 c2_mode r0_mode) := by
    exact Iff.mp (normalization_5718 c2_mode r0_mode) (replay_3478 c2_mode r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5719 c2_mode r0_mode) hn

theorem normalized_1417 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5720 (c2_level r0_level : Int) : (r0_level ≤ c2_level) ↔ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5721 (c2_level r0_level : Int) : (r0_level ≥ c2_level) ↔ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5722 (c2_level r0_level : Int) : ((r0_level ≤ c2_level) ∧ (r0_level ≥ c2_level)) ↔ ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := (and_congr (normalization_5720 c2_level r0_level) (normalization_5721 c2_level r0_level))

abbrev shared_expr_Repair060_3 (c2_level r0_level : Int) : Prop := (((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))))
theorem normalization_5723 (c2_level r0_level : Int) : ((r0_level = c2_level) ↔ ((r0_level ≤ c2_level) ∧ (r0_level ≥ c2_level))) ↔ (shared_expr_Repair060_3 c2_level r0_level) := (iff_congr (normalization_5517 c2_level r0_level) (normalization_5722 c2_level r0_level))

-- Checked replay of rewrite.
theorem replay_3480 (c2_level r0_level : Int) : ((r0_level = c2_level) ↔ ((r0_level ≤ c2_level) ∧ (r0_level ≥ c2_level))) := by
  classical
  have ht := (normalized_1417 ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5723 c2_level r0_level) hn

theorem normalized_1418 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5724 (c2_level r0_level : Int) : ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ↔ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5725 (c2_level r0_level : Int) : ((r0_level ≤ c2_level) ↔ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_5720 c2_level r0_level) (normalization_5724 c2_level r0_level))

-- Checked replay of rewrite.
theorem replay_3481 (c2_level r0_level : Int) : ((r0_level ≤ c2_level) ↔ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1418 ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5725 c2_level r0_level) hn

theorem normalized_1419 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5726 (c2_level r0_level : Int) : ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5727 (c2_level r0_level : Int) : ((r0_level ≥ c2_level) ↔ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := (iff_congr (normalization_5721 c2_level r0_level) (normalization_5726 c2_level r0_level))

-- Checked replay of rewrite.
theorem replay_3482 (c2_level r0_level : Int) : ((r0_level ≥ c2_level) ↔ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1419 ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5727 c2_level r0_level) hn

theorem normalized_1420 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5728 (c2_level r0_level : Int) : (((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := (and_congr (normalization_5724 c2_level r0_level) (normalization_5726 c2_level r0_level))

theorem normalization_5729 (c2_level r0_level : Int) : (((r0_level ≤ c2_level) ∧ (r0_level ≥ c2_level)) ↔ (((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ (shared_expr_Repair060_3 c2_level r0_level) := (iff_congr (normalization_5722 c2_level r0_level) (normalization_5728 c2_level r0_level))

-- Checked replay of monotonicity.
theorem replay_3483 (c2_level r0_level : Int) : (((r0_level ≤ c2_level) ∧ (r0_level ≥ c2_level)) ↔ (((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1420 ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5725 c2_level r0_level) (replay_3481 c2_level r0_level)
  have n1 : (((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5727 c2_level r0_level) (replay_3482 c2_level r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5729 c2_level r0_level) hn

abbrev shared_expr_Repair060_4 (c2_level r0_level : Int) : Prop := ((((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))))
abbrev formula_1699 (c2_level r0_level : Int) : Prop := (shared_expr_Repair060_4 c2_level r0_level)

theorem normalized_1421 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5730 (c2_level r0_level : Int) : (¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5724 c2_level r0_level))

theorem normalization_5731 (c2_level r0_level : Int) : (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := (not_congr (normalization_5726 c2_level r0_level))

theorem normalization_5732 (c2_level r0_level : Int) : ((¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)))) := (or_congr (normalization_5730 c2_level r0_level) (normalization_5731 c2_level r0_level))

theorem normalization_5733 (c2_level r0_level : Int) : (¬ ((¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))))) := (not_congr (normalization_5732 c2_level r0_level))

abbrev shared_expr_Repair060_5 (c2_level r0_level : Int) : Prop := (((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))))))
theorem normalization_5734 (c2_level r0_level : Int) : (formula_1699 c2_level r0_level) ↔ (shared_expr_Repair060_5 c2_level r0_level) := (iff_congr (normalization_5728 c2_level r0_level) (normalization_5733 c2_level r0_level))

-- Checked replay of rewrite.
theorem replay_3484 (c2_level r0_level : Int) : (formula_1699 c2_level r0_level) := by
  classical
  have ht := (normalized_1421 ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5734 c2_level r0_level) hn

theorem normalized_1422 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5735 (c2_level r0_level : Int) : (((r0_level ≤ c2_level) ∧ (r0_level ≥ c2_level)) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair060_5 c2_level r0_level) := (iff_congr (normalization_5722 c2_level r0_level) (normalization_5733 c2_level r0_level))

-- Checked replay of trans.
theorem replay_3485 (c2_level r0_level : Int) : (((r0_level ≤ c2_level) ∧ (r0_level ≥ c2_level)) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1422 ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) (shared_expr_Repair060_5 c2_level r0_level))
  have n0 : (shared_expr_Repair060_3 c2_level r0_level) := by
    exact Iff.mp (normalization_5729 c2_level r0_level) (replay_3483 c2_level r0_level)
  have n1 : (shared_expr_Repair060_5 c2_level r0_level) := by
    exact Iff.mp (normalization_5734 c2_level r0_level) (replay_3484 c2_level r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5735 c2_level r0_level) hn

theorem normalized_1423 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5736 (c2_level r0_level : Int) : ((r0_level = c2_level) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair060_5 c2_level r0_level) := (iff_congr (normalization_5517 c2_level r0_level) (normalization_5733 c2_level r0_level))

-- Checked replay of trans.
theorem replay_3486 (c2_level r0_level : Int) : ((r0_level = c2_level) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1423 ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) (shared_expr_Repair060_5 c2_level r0_level))
  have n0 : (shared_expr_Repair060_3 c2_level r0_level) := by
    exact Iff.mp (normalization_5723 c2_level r0_level) (replay_3480 c2_level r0_level)
  have n1 : (shared_expr_Repair060_5 c2_level r0_level) := by
    exact Iff.mp (normalization_5735 c2_level r0_level) (replay_3485 c2_level r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5736 c2_level r0_level) hn

theorem normalized_1424 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5737 (c2_group r0_group : Int) : (r0_group ≤ c2_group) ↔ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5738 (c2_group r0_group : Int) : (r0_group ≥ c2_group) ↔ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_5739 (c2_group r0_group : Int) : ((r0_group ≤ c2_group) ∧ (r0_group ≥ c2_group)) ↔ ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) := (and_congr (normalization_5737 c2_group r0_group) (normalization_5738 c2_group r0_group))

abbrev shared_expr_Repair060_6 (c2_group r0_group : Int) : Prop := (((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))))
theorem normalization_5740 (c2_group r0_group : Int) : ((r0_group = c2_group) ↔ ((r0_group ≤ c2_group) ∧ (r0_group ≥ c2_group))) ↔ (shared_expr_Repair060_6 c2_group r0_group) := (iff_congr (normalization_5589 c2_group r0_group) (normalization_5739 c2_group r0_group))

-- Checked replay of rewrite.
theorem replay_3487 (c2_group r0_group : Int) : ((r0_group = c2_group) ↔ ((r0_group ≤ c2_group) ∧ (r0_group ≥ c2_group))) := by
  classical
  have ht := (normalized_1424 ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5740 c2_group r0_group) hn

theorem normalized_1425 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5741 (c2_group r0_group : Int) : ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ↔ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5742 (c2_group r0_group : Int) : ((r0_group ≤ c2_group) ↔ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_5737 c2_group r0_group) (normalization_5741 c2_group r0_group))

-- Checked replay of rewrite.
theorem replay_3488 (c2_group r0_group : Int) : ((r0_group ≤ c2_group) ↔ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1425 ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5742 c2_group r0_group) hn

theorem normalized_1426 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5743 (c2_group r0_group : Int) : ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_5744 (c2_group r0_group : Int) : ((r0_group ≥ c2_group) ↔ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) := (iff_congr (normalization_5738 c2_group r0_group) (normalization_5743 c2_group r0_group))

-- Checked replay of rewrite.
theorem replay_3489 (c2_group r0_group : Int) : ((r0_group ≥ c2_group) ↔ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1426 ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5744 c2_group r0_group) hn

theorem normalized_1427 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5745 (c2_group r0_group : Int) : (((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) := (and_congr (normalization_5741 c2_group r0_group) (normalization_5743 c2_group r0_group))

theorem normalization_5746 (c2_group r0_group : Int) : (((r0_group ≤ c2_group) ∧ (r0_group ≥ c2_group)) ↔ (((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ↔ (shared_expr_Repair060_6 c2_group r0_group) := (iff_congr (normalization_5739 c2_group r0_group) (normalization_5745 c2_group r0_group))

-- Checked replay of monotonicity.
theorem replay_3490 (c2_group r0_group : Int) : (((r0_group ≤ c2_group) ∧ (r0_group ≥ c2_group)) ↔ (((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1427 ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)) ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5742 c2_group r0_group) (replay_3488 c2_group r0_group)
  have n1 : (((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5744 c2_group r0_group) (replay_3489 c2_group r0_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5746 c2_group r0_group) hn

abbrev shared_expr_Repair060_7 (c2_group r0_group : Int) : Prop := ((((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))
abbrev formula_1700 (c2_group r0_group : Int) : Prop := (shared_expr_Repair060_7 c2_group r0_group)

theorem normalized_1428 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5747 (c2_group r0_group : Int) : (¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) := (not_congr (normalization_5741 c2_group r0_group))

theorem normalization_5748 (c2_group r0_group : Int) : (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) := (not_congr (normalization_5743 c2_group r0_group))

theorem normalization_5749 (c2_group r0_group : Int) : ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))) := (or_congr (normalization_5747 c2_group r0_group) (normalization_5748 c2_group r0_group))

theorem normalization_5750 (c2_group r0_group : Int) : (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))))) := (not_congr (normalization_5749 c2_group r0_group))

abbrev shared_expr_Repair060_8 (c2_group r0_group : Int) : Prop := (((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))))))
theorem normalization_5751 (c2_group r0_group : Int) : (formula_1700 c2_group r0_group) ↔ (shared_expr_Repair060_8 c2_group r0_group) := (iff_congr (normalization_5745 c2_group r0_group) (normalization_5750 c2_group r0_group))

-- Checked replay of rewrite.
theorem replay_3491 (c2_group r0_group : Int) : (formula_1700 c2_group r0_group) := by
  classical
  have ht := (normalized_1428 ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5751 c2_group r0_group) hn

theorem normalized_1429 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5752 (c2_group r0_group : Int) : (((r0_group ≤ c2_group) ∧ (r0_group ≥ c2_group)) ↔ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair060_8 c2_group r0_group) := (iff_congr (normalization_5739 c2_group r0_group) (normalization_5750 c2_group r0_group))

-- Checked replay of trans.
theorem replay_3492 (c2_group r0_group : Int) : (((r0_group ≤ c2_group) ∧ (r0_group ≥ c2_group)) ↔ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1429 ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) (shared_expr_Repair060_8 c2_group r0_group))
  have n0 : (shared_expr_Repair060_6 c2_group r0_group) := by
    exact Iff.mp (normalization_5746 c2_group r0_group) (replay_3490 c2_group r0_group)
  have n1 : (shared_expr_Repair060_8 c2_group r0_group) := by
    exact Iff.mp (normalization_5751 c2_group r0_group) (replay_3491 c2_group r0_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5752 c2_group r0_group) hn

theorem normalized_1430 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5753 (c2_group r0_group : Int) : ((r0_group = c2_group) ↔ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair060_8 c2_group r0_group) := (iff_congr (normalization_5589 c2_group r0_group) (normalization_5750 c2_group r0_group))

-- Checked replay of trans.
theorem replay_3493 (c2_group r0_group : Int) : ((r0_group = c2_group) ↔ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1430 ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) (shared_expr_Repair060_8 c2_group r0_group))
  have n0 : (shared_expr_Repair060_6 c2_group r0_group) := by
    exact Iff.mp (normalization_5740 c2_group r0_group) (replay_3487 c2_group r0_group)
  have n1 : (shared_expr_Repair060_8 c2_group r0_group) := by
    exact Iff.mp (normalization_5752 c2_group r0_group) (replay_3492 c2_group r0_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5753 c2_group r0_group) hn

theorem normalized_1431 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5754 (c2_group r0_group : Int) : (¬ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))) := (not_congr (normalization_5750 c2_group r0_group))

abbrev shared_expr_Repair060_9 (c2_group r0_group : Int) : Prop := ((¬ ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))))
theorem normalization_5755 (c2_group r0_group : Int) : ((¬ (r0_group = c2_group)) ↔ (¬ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Repair060_9 c2_group r0_group) := (iff_congr (normalization_5590 c2_group r0_group) (normalization_5754 c2_group r0_group))

-- Checked replay of monotonicity.
theorem replay_3494 (c2_group r0_group : Int) : ((¬ (r0_group = c2_group)) ↔ (¬ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1431 ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair060_8 c2_group r0_group) := by
    exact Iff.mp (normalization_5753 c2_group r0_group) (replay_3493 c2_group r0_group)
  have hn := ht n0
  exact Iff.mpr (normalization_5755 c2_group r0_group) hn

abbrev shared_expr_Repair060_10 (c2_group r0_group : Int) : Prop := ((¬ (¬ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))
abbrev formula_1701 (c2_group r0_group : Int) : Prop := (shared_expr_Repair060_10 c2_group r0_group)

theorem normalized_1432 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_11 (c2_group r0_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
theorem normalization_5756 (c2_group r0_group : Int) : (formula_1701 c2_group r0_group) ↔ (shared_expr_Repair060_11 c2_group r0_group) := (iff_congr (normalization_5754 c2_group r0_group) (normalization_5749 c2_group r0_group))

-- Checked replay of rewrite.
theorem replay_3495 (c2_group r0_group : Int) : (formula_1701 c2_group r0_group) := by
  classical
  have ht := (normalized_1432 ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5756 c2_group r0_group) hn

theorem normalized_1433 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_12 (c2_group r0_group : Int) : Prop := ((¬ ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
theorem normalization_5757 (c2_group r0_group : Int) : ((¬ (r0_group = c2_group)) ↔ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) ↔ (shared_expr_Repair060_12 c2_group r0_group) := (iff_congr (normalization_5590 c2_group r0_group) (normalization_5749 c2_group r0_group))

-- Checked replay of trans.
theorem replay_3496 (c2_group r0_group : Int) : ((¬ (r0_group = c2_group)) ↔ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1433 ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair060_9 c2_group r0_group) := by
    exact Iff.mp (normalization_5755 c2_group r0_group) (replay_3494 c2_group r0_group)
  have n1 : (shared_expr_Repair060_11 c2_group r0_group) := by
    exact Iff.mp (normalization_5756 c2_group r0_group) (replay_3495 c2_group r0_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5757 c2_group r0_group) hn

abbrev shared_expr_Repair060_13 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : Prop := ((¬ ((¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))) ∧ ((¬ ((r0_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))
abbrev formula_1702 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair060_13 c2_group c2_level c2_mode r0_group r0_level r0_mode)

theorem normalized_1434 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_14 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : Prop := ((¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
theorem normalization_5758 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : (formula_1702 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (shared_expr_Repair060_14 c2_group c2_level c2_mode r0_group r0_level r0_mode) := (and_congr (normalization_5716 c2_mode r0_mode) (and_congr (normalization_5733 c2_level r0_level) (normalization_5749 c2_group r0_group)))

abbrev shared_expr_Repair060_15 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ∧ ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
theorem normalization_5759 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : (((r0_mode = c2_mode) ∧ (r0_level = c2_level) ∧ (¬ (r0_group = c2_group))) ↔ (formula_1702 c2_group c2_level c2_mode r0_group r0_level r0_mode)) ↔ ((shared_expr_Repair060_15 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (shared_expr_Repair060_14 c2_group c2_level c2_mode r0_group r0_level r0_mode)) := (iff_congr (normalization_5591 c2_group c2_level c2_mode r0_group r0_level r0_mode) (normalization_5758 c2_group c2_level c2_mode r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_3497 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : (((r0_mode = c2_mode) ∧ (r0_level = c2_level) ∧ (¬ (r0_group = c2_group))) ↔ (formula_1702 c2_group c2_level c2_mode r0_group r0_level r0_mode)) := by
  classical
  have ht := (normalized_1434 ((¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ((¬ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)))) ((¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ((¬ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)))) ((¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair060_2 c2_mode r0_mode) := by
    exact Iff.mp (normalization_5719 c2_mode r0_mode) (replay_3479 c2_mode r0_mode)
  have n1 : (shared_expr_Repair060_5 c2_level r0_level) := by
    exact Iff.mp (normalization_5736 c2_level r0_level) (replay_3486 c2_level r0_level)
  have n2 : (shared_expr_Repair060_12 c2_group r0_group) := by
    exact Iff.mp (normalization_5757 c2_group r0_group) (replay_3496 c2_group r0_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5759 c2_group c2_level c2_mode r0_group r0_level r0_mode) hn

theorem normalized_1435 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_16 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : Prop := ((¬ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))))))
theorem normalization_5760 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : (formula_1589 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (shared_expr_Repair060_16 c2_group c2_level c2_mode r0_group r0_level r0_mode) := (or_congr (normalization_5713 c2_mode r0_mode) (or_congr (normalization_5714 c2_mode r0_mode) (or_congr (normalization_5730 c2_level r0_level) (or_congr (normalization_5731 c2_level r0_level) (normalization_5750 c2_group r0_group)))))

theorem normalization_5761 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : (¬ (formula_1589 c2_group c2_level c2_mode r0_group r0_level r0_mode)) ↔ (¬ (shared_expr_Repair060_16 c2_group c2_level c2_mode r0_group r0_level r0_mode)) := (not_congr (normalization_5760 c2_group c2_level c2_mode r0_group r0_level r0_mode))

theorem normalization_5762 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : ((formula_1702 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (¬ (formula_1589 c2_group c2_level c2_mode r0_group r0_level r0_mode))) ↔ ((shared_expr_Repair060_14 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (¬ (shared_expr_Repair060_16 c2_group c2_level c2_mode r0_group r0_level r0_mode))) := (iff_congr (normalization_5758 c2_group c2_level c2_mode r0_group r0_level r0_mode) (normalization_5761 c2_group c2_level c2_mode r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_3498 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : ((formula_1702 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (¬ (formula_1589 c2_group c2_level c2_mode r0_group r0_level r0_mode))) := by
  classical
  have ht := (normalized_1435 ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((¬ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5762 c2_group c2_level c2_mode r0_group r0_level r0_mode) hn

theorem normalized_1436 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5763 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : (((r0_mode = c2_mode) ∧ (r0_level = c2_level) ∧ (¬ (r0_group = c2_group))) ↔ (¬ (formula_1589 c2_group c2_level c2_mode r0_group r0_level r0_mode))) ↔ ((shared_expr_Repair060_15 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (¬ (shared_expr_Repair060_16 c2_group c2_level c2_mode r0_group r0_level r0_mode))) := (iff_congr (normalization_5591 c2_group c2_level c2_mode r0_group r0_level r0_mode) (normalization_5761 c2_group c2_level c2_mode r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_3499 (c2_group c2_level c2_mode r0_group r0_level r0_mode : Int) : (((r0_mode = c2_mode) ∧ (r0_level = c2_level) ∧ (¬ (r0_group = c2_group))) ↔ (¬ (formula_1589 c2_group c2_level c2_mode r0_group r0_level r0_mode))) := by
  classical
  have ht := (normalized_1436 (shared_expr_Repair060_15 c2_group c2_level c2_mode r0_group r0_level r0_mode) (shared_expr_Repair060_14 c2_group c2_level c2_mode r0_group r0_level r0_mode) (shared_expr_Repair060_16 c2_group c2_level c2_mode r0_group r0_level r0_mode))
  have n0 : ((shared_expr_Repair060_15 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (shared_expr_Repair060_14 c2_group c2_level c2_mode r0_group r0_level r0_mode)) := by
    exact Iff.mp (normalization_5759 c2_group c2_level c2_mode r0_group r0_level r0_mode) (replay_3497 c2_group c2_level c2_mode r0_group r0_level r0_mode)
  have n1 : ((shared_expr_Repair060_14 c2_group c2_level c2_mode r0_group r0_level r0_mode) ↔ (¬ (shared_expr_Repair060_16 c2_group c2_level c2_mode r0_group r0_level r0_mode))) := by
    exact Iff.mp (normalization_5762 c2_group c2_level c2_mode r0_group r0_level r0_mode) (replay_3498 c2_group c2_level c2_mode r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5763 c2_group c2_level c2_mode r0_group r0_level r0_mode) hn

theorem normalized_1437 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5764 (c2_depth r0_level : Int) : ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_5765 (c2_depth r0_level : Int) : ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ↔ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5766 (c2_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := (and_congr (normalization_5764 c2_depth r0_level) (normalization_5765 c2_depth r0_level))

abbrev shared_expr_Repair060_17 (c2_depth r0_level : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))
theorem normalization_5767 (c2_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Repair060_17 c2_depth r0_level) := (iff_congr (normalization_5657 c2_depth r0_level) (normalization_5766 c2_depth r0_level))

-- Checked replay of rewrite.
theorem replay_3500 (c2_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1437 ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5767 c2_depth r0_level) hn

abbrev shared_expr_Repair060_18 (c2_depth r0_level : Int) : Prop := ((((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))
abbrev formula_1703 (c2_depth r0_level : Int) : Prop := (shared_expr_Repair060_18 c2_depth r0_level)

theorem normalized_1438 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5768 (c2_depth r0_level : Int) : (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) := (not_congr (normalization_5764 c2_depth r0_level))

theorem normalization_5769 (c2_depth r0_level : Int) : (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := (not_congr (normalization_5765 c2_depth r0_level))

theorem normalization_5770 (c2_depth r0_level : Int) : ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (or_congr (normalization_5768 c2_depth r0_level) (normalization_5769 c2_depth r0_level))

theorem normalization_5771 (c2_depth r0_level : Int) : (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) := (not_congr (normalization_5770 c2_depth r0_level))

abbrev shared_expr_Repair060_19 (c2_depth r0_level : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))))
theorem normalization_5772 (c2_depth r0_level : Int) : (formula_1703 c2_depth r0_level) ↔ (shared_expr_Repair060_19 c2_depth r0_level) := (iff_congr (normalization_5766 c2_depth r0_level) (normalization_5771 c2_depth r0_level))

-- Checked replay of rewrite.
theorem replay_3501 (c2_depth r0_level : Int) : (formula_1703 c2_depth r0_level) := by
  classical
  have ht := (normalized_1438 ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5772 c2_depth r0_level) hn

theorem normalized_1439 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5773 (c2_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Repair060_19 c2_depth r0_level) := (iff_congr (normalization_5657 c2_depth r0_level) (normalization_5771 c2_depth r0_level))

-- Checked replay of trans.
theorem replay_3502 (c2_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1439 ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) (shared_expr_Repair060_19 c2_depth r0_level))
  have n0 : (shared_expr_Repair060_17 c2_depth r0_level) := by
    exact Iff.mp (normalization_5767 c2_depth r0_level) (replay_3500 c2_depth r0_level)
  have n1 : (shared_expr_Repair060_19 c2_depth r0_level) := by
    exact Iff.mp (normalization_5772 c2_depth r0_level) (replay_3501 c2_depth r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5773 c2_depth r0_level) hn

theorem normalized_1440 (p0 p1 p2 p3 : Prop) : (((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_20 (c2_sign : Int) : Prop := (((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
theorem normalization_5774 (c2_sign : Int) : (((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ↔ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) ↔ (shared_expr_Repair060_20 c2_sign) := (iff_congr (normalization_809 c2_sign) (normalization_1067 c2_sign))

-- Checked replay of rewrite.
theorem replay_3503 (c2_sign : Int) : (((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ↔ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_1440 ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) ((c2_sign) ≤ (2 : Int)) ((c2_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5774 c2_sign) hn

abbrev shared_expr_Repair060_21 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ∧ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))))
abbrev formula_1704 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := (shared_expr_Repair060_21 c2_depth c2_kind c2_sign r0_level)

theorem normalized_1441 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → ((p0 ∧ p2 ∧ p4) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_22 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
theorem normalization_5775 (c2_depth c2_kind c2_sign r0_level : Int) : (formula_1704 c2_depth c2_kind c2_sign r0_level) ↔ (shared_expr_Repair060_22 c2_depth c2_kind c2_sign r0_level) := (and_congr (normalization_3071 c2_kind) (and_congr (normalization_5771 c2_depth r0_level) (normalization_1067 c2_sign)))

abbrev shared_expr_Repair060_23 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
theorem normalization_5776 (c2_depth c2_kind c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (formula_1704 c2_depth c2_kind c2_sign r0_level)) ↔ ((shared_expr_Repair060_23 c2_depth c2_kind c2_sign r0_level) ↔ (shared_expr_Repair060_22 c2_depth c2_kind c2_sign r0_level)) := (iff_congr (normalization_5658 c2_depth c2_kind c2_sign r0_level) (normalization_5775 c2_depth c2_kind c2_sign r0_level))

-- Checked replay of monotonicity.
theorem replay_3504 (c2_depth c2_kind c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (formula_1704 c2_depth c2_kind c2_sign r0_level)) := by
  classical
  have ht := (normalized_1441 (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ((¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
  have n0 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3073 c2_kind) (replay_2154 c2_kind)
  have n1 : (shared_expr_Repair060_19 c2_depth r0_level) := by
    exact Iff.mp (normalization_5773 c2_depth r0_level) (replay_3502 c2_depth r0_level)
  have n2 : (shared_expr_Repair060_20 c2_sign) := by
    exact Iff.mp (normalization_5774 c2_sign) (replay_3503 c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5776 c2_depth c2_kind c2_sign r0_level) hn

theorem normalized_1442 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_24 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))))
theorem normalization_5777 (c2_depth c2_kind c2_sign r0_level : Int) : (formula_1590 c2_depth c2_kind c2_sign r0_level) ↔ (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_5768 c2_depth r0_level) (or_congr (normalization_5769 c2_depth r0_level) (normalization_1068 c2_sign)))))

theorem normalization_5778 (c2_depth c2_kind c2_sign r0_level : Int) : (¬ (formula_1590 c2_depth c2_kind c2_sign r0_level)) ↔ (¬ (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level)) := (not_congr (normalization_5777 c2_depth c2_kind c2_sign r0_level))

theorem normalization_5779 (c2_depth c2_kind c2_sign r0_level : Int) : ((formula_1704 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (formula_1590 c2_depth c2_kind c2_sign r0_level))) ↔ ((shared_expr_Repair060_22 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))) := (iff_congr (normalization_5775 c2_depth c2_kind c2_sign r0_level) (normalization_5778 c2_depth c2_kind c2_sign r0_level))

-- Checked replay of rewrite.
theorem replay_3505 (c2_depth c2_kind c2_sign r0_level : Int) : ((formula_1704 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (formula_1590 c2_depth c2_kind c2_sign r0_level))) := by
  classical
  have ht := (normalized_1442 ((c2_kind) ≤ (1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
  have hn := ht
  exact Iff.mpr (normalization_5779 c2_depth c2_kind c2_sign r0_level) hn

theorem normalized_1443 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5780 (c2_depth c2_kind c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (¬ (formula_1590 c2_depth c2_kind c2_sign r0_level))) ↔ ((shared_expr_Repair060_23 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))) := (iff_congr (normalization_5658 c2_depth c2_kind c2_sign r0_level) (normalization_5778 c2_depth c2_kind c2_sign r0_level))

-- Checked replay of trans.
theorem replay_3506 (c2_depth c2_kind c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (¬ (formula_1590 c2_depth c2_kind c2_sign r0_level))) := by
  classical
  have ht := (normalized_1443 (shared_expr_Repair060_23 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair060_22 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))
  have n0 : ((shared_expr_Repair060_23 c2_depth c2_kind c2_sign r0_level) ↔ (shared_expr_Repair060_22 c2_depth c2_kind c2_sign r0_level)) := by
    exact Iff.mp (normalization_5776 c2_depth c2_kind c2_sign r0_level) (replay_3504 c2_depth c2_kind c2_sign r0_level)
  have n1 : ((shared_expr_Repair060_22 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))) := by
    exact Iff.mp (normalization_5779 c2_depth c2_kind c2_sign r0_level) (replay_3505 c2_depth c2_kind c2_sign r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5780 c2_depth c2_kind c2_sign r0_level) hn

abbrev shared_expr_Repair060_25 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ∨ ((¬ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ∧ (¬ (formula_1590 c2_depth c2_kind c2_sign r0_level))))
abbrev formula_1705 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (shared_expr_Repair060_25 c2_depth c2_kind c2_sign r0_group r0_level)

theorem normalized_1444 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_26 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))))
theorem normalization_5781 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : (formula_1705 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_26 c2_depth c2_kind c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1764 r0_group) (normalization_1076 c2_kind)) (and_congr (not_congr (normalization_1764 r0_group)) (normalization_5778 c2_depth c2_kind c2_sign r0_level)))

abbrev shared_expr_Repair060_27 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair060_23 c2_depth c2_kind c2_sign r0_level)))
theorem normalization_5782 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1681 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1705 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_26 c2_depth c2_kind c2_sign r0_group r0_level)) := (iff_congr (normalization_5659 c2_depth c2_kind c2_sign r0_group r0_level) (normalization_5781 c2_depth c2_kind c2_sign r0_group r0_level))

-- Checked replay of monotonicity.
theorem replay_3507 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1681 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1705 c2_depth c2_kind c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1444 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (shared_expr_Repair060_23 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1766 r0_group) (replay_352 r0_group)
  have n1 : ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3077 c2_kind) (replay_2157 c2_kind)
  have n2 : ((shared_expr_Repair060_23 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))) := by
    exact Iff.mp (normalization_5780 c2_depth c2_kind c2_sign r0_level) (replay_3506 c2_depth c2_kind c2_sign r0_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5782 c2_depth c2_kind c2_sign r0_group r0_level) hn

theorem normalized_1445 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_28 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
theorem normalization_5783 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1763 r0_group) (normalization_5778 c2_depth c2_kind c2_sign r0_level)) (and_congr (not_congr (normalization_1763 r0_group)) (normalization_1076 c2_kind)))

theorem normalization_5784 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1705 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair060_26 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)) := (iff_congr (normalization_5781 c2_depth c2_kind c2_sign r0_group r0_level) (normalization_5783 c2_depth c2_kind c2_sign r0_group r0_level))

-- Checked replay of rewrite.
theorem replay_3508 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1705 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1445 ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (shared_expr_Repair060_24 c2_depth c2_kind c2_sign r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5784 c2_depth c2_kind c2_sign r0_group r0_level) hn

theorem normalized_1446 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5785 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1681 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)) := (iff_congr (normalization_5659 c2_depth c2_kind c2_sign r0_group r0_level) (normalization_5783 c2_depth c2_kind c2_sign r0_group r0_level))

-- Checked replay of trans.
theorem replay_3509 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1681 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1446 (shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level) (shared_expr_Repair060_26 c2_depth c2_kind c2_sign r0_group r0_level) (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level))
  have n0 : ((shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_26 c2_depth c2_kind c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5782 c2_depth c2_kind c2_sign r0_group r0_level) (replay_3507 c2_depth c2_kind c2_sign r0_group r0_level)
  have n1 : ((shared_expr_Repair060_26 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5784 c2_depth c2_kind c2_sign r0_group r0_level) (replay_3508 c2_depth c2_kind c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5785 c2_depth c2_kind c2_sign r0_group r0_level) hn

abbrev shared_expr_Repair060_29 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (0 : Int)) ∧ (formula_1681 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((¬ ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int))))) ∧ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)))
abbrev formula_1706 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair060_29 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)

theorem normalized_1447 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5786 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : ((¬ ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int))))) ∧ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)) := (and_congr (normalization_1754 r0_mode) (normalization_5783 c2_depth c2_kind c2_sign r0_group r0_level))

abbrev shared_expr_Repair060_30 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)))
theorem normalization_5787 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1706 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair060_30 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5660 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (normalization_5786 c2_depth c2_kind c2_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_3510 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1706 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1447 (((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int))))) (shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level) (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level))
  have n0 : ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1756 r0_mode) (replay_349 r0_mode)
  have n1 : ((shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5785 c2_depth c2_kind c2_sign r0_group r0_level) (replay_3509 c2_depth c2_kind c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5787 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair060_31 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int))))) ∧ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)))))
abbrev formula_1707 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair060_31 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)

theorem normalized_1448 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ (¬ p1)) ∨ (¬ p0) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5788 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : (¬ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)) := (not_congr (normalization_5783 c2_depth c2_kind c2_sign r0_group r0_level))

theorem normalization_5789 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : ((¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level))) ↔ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level))) := (or_congr (normalization_1752 r0_mode) (or_congr (normalization_1751 r0_mode) (normalization_5788 c2_depth c2_kind c2_sign r0_group r0_level)))

theorem normalization_5790 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (¬ ((¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)))) ↔ (¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)))) := (not_congr (normalization_5789 c2_depth c2_kind c2_sign r0_group r0_level r0_mode))

abbrev shared_expr_Repair060_32 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)))))
theorem normalization_5791 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1707 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair060_32 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5786 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (normalization_5790 c2_depth c2_kind c2_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_3511 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1707 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1448 ((r0_mode) ≤ (0 : Int)) ((r0_mode) ≤ (-1 : Int)) (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5791 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair060_33 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (0 : Int)) ∧ (formula_1681 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (formula_1591 c2_depth c2_kind c2_sign r0_group r0_level)))))
abbrev formula_1708 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair060_33 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)

theorem normalized_1449 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_34 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ (¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)))))
theorem normalization_5792 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1708 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair060_34 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5660 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (normalization_5790 c2_depth c2_kind c2_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_3512 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1708 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1449 ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair060_27 c2_depth c2_kind c2_sign r0_group r0_level)) ((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level)) ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair060_28 c2_depth c2_kind c2_sign r0_group r0_level))))
  have n0 : (shared_expr_Repair060_30 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5787 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (replay_3510 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)
  have n1 : (shared_expr_Repair060_32 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_5791 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (replay_3511 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5792 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) hn

theorem normalized_1450 (p0 p1 p2 : Prop) : (((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p0))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p0)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_35 (c2_sign : Int) : Prop := (((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
theorem normalization_5793 (c2_sign : Int) : (((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ↔ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) ↔ (shared_expr_Repair060_35 c2_sign) := (iff_congr (normalization_813 c2_sign) (normalization_1081 c2_sign))

-- Checked replay of rewrite.
theorem replay_3513 (c2_sign : Int) : (((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ↔ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_1450 ((c2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5793 c2_sign) hn

abbrev shared_expr_Repair060_36 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ∧ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))))
abbrev formula_1709 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := (shared_expr_Repair060_36 c2_depth c2_kind c2_sign r0_level)

theorem normalized_1451 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → ((p0 ∧ p2 ∧ p4) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_37 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
theorem normalization_5794 (c2_depth c2_kind c2_sign r0_level : Int) : (formula_1709 c2_depth c2_kind c2_sign r0_level) ↔ (shared_expr_Repair060_37 c2_depth c2_kind c2_sign r0_level) := (and_congr (normalization_3071 c2_kind) (and_congr (normalization_5771 c2_depth r0_level) (normalization_1081 c2_sign)))

abbrev shared_expr_Repair060_38 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
theorem normalization_5795 (c2_depth c2_kind c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (formula_1709 c2_depth c2_kind c2_sign r0_level)) ↔ ((shared_expr_Repair060_38 c2_depth c2_kind c2_sign r0_level) ↔ (shared_expr_Repair060_37 c2_depth c2_kind c2_sign r0_level)) := (iff_congr (normalization_5661 c2_depth c2_kind c2_sign r0_level) (normalization_5794 c2_depth c2_kind c2_sign r0_level))

-- Checked replay of monotonicity.
theorem replay_3514 (c2_depth c2_kind c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (formula_1709 c2_depth c2_kind c2_sign r0_level)) := by
  classical
  have ht := (normalized_1451 (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) ((¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ((¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
  have n0 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3073 c2_kind) (replay_2154 c2_kind)
  have n1 : (shared_expr_Repair060_19 c2_depth r0_level) := by
    exact Iff.mp (normalization_5773 c2_depth r0_level) (replay_3502 c2_depth r0_level)
  have n2 : (shared_expr_Repair060_35 c2_sign) := by
    exact Iff.mp (normalization_5793 c2_sign) (replay_3513 c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5795 c2_depth c2_kind c2_sign r0_level) hn

theorem normalized_1452 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_39 (c2_depth c2_kind c2_sign r0_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))))
theorem normalization_5796 (c2_depth c2_kind c2_sign r0_level : Int) : (formula_1592 c2_depth c2_kind c2_sign r0_level) ↔ (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_5768 c2_depth r0_level) (or_congr (normalization_5769 c2_depth r0_level) (normalization_1082 c2_sign)))))

theorem normalization_5797 (c2_depth c2_kind c2_sign r0_level : Int) : (¬ (formula_1592 c2_depth c2_kind c2_sign r0_level)) ↔ (¬ (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level)) := (not_congr (normalization_5796 c2_depth c2_kind c2_sign r0_level))

theorem normalization_5798 (c2_depth c2_kind c2_sign r0_level : Int) : ((formula_1709 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (formula_1592 c2_depth c2_kind c2_sign r0_level))) ↔ ((shared_expr_Repair060_37 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))) := (iff_congr (normalization_5794 c2_depth c2_kind c2_sign r0_level) (normalization_5797 c2_depth c2_kind c2_sign r0_level))

-- Checked replay of rewrite.
theorem replay_3515 (c2_depth c2_kind c2_sign r0_level : Int) : ((formula_1709 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (formula_1592 c2_depth c2_kind c2_sign r0_level))) := by
  classical
  have ht := (normalized_1452 ((c2_kind) ≤ (1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)) ((c2_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))))
  have hn := ht
  exact Iff.mpr (normalization_5798 c2_depth c2_kind c2_sign r0_level) hn

theorem normalized_1453 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5799 (c2_depth c2_kind c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (¬ (formula_1592 c2_depth c2_kind c2_sign r0_level))) ↔ ((shared_expr_Repair060_38 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))) := (iff_congr (normalization_5661 c2_depth c2_kind c2_sign r0_level) (normalization_5797 c2_depth c2_kind c2_sign r0_level))

-- Checked replay of trans.
theorem replay_3516 (c2_depth c2_kind c2_sign r0_level : Int) : (((c2_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (¬ (formula_1592 c2_depth c2_kind c2_sign r0_level))) := by
  classical
  have ht := (normalized_1453 (shared_expr_Repair060_38 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair060_37 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))
  have n0 : ((shared_expr_Repair060_38 c2_depth c2_kind c2_sign r0_level) ↔ (shared_expr_Repair060_37 c2_depth c2_kind c2_sign r0_level)) := by
    exact Iff.mp (normalization_5795 c2_depth c2_kind c2_sign r0_level) (replay_3514 c2_depth c2_kind c2_sign r0_level)
  have n1 : ((shared_expr_Repair060_37 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))) := by
    exact Iff.mp (normalization_5798 c2_depth c2_kind c2_sign r0_level) (replay_3515 c2_depth c2_kind c2_sign r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5799 c2_depth c2_kind c2_sign r0_level) hn

abbrev shared_expr_Repair060_40 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ∨ ((¬ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ∧ (¬ (formula_1592 c2_depth c2_kind c2_sign r0_level))))
abbrev formula_1710 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (shared_expr_Repair060_40 c2_depth c2_kind c2_sign r0_group r0_level)

theorem normalized_1454 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_41 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))))
theorem normalization_5800 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : (formula_1710 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_41 c2_depth c2_kind c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1764 r0_group) (normalization_1076 c2_kind)) (and_congr (not_congr (normalization_1764 r0_group)) (normalization_5797 c2_depth c2_kind c2_sign r0_level)))

abbrev shared_expr_Repair060_42 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair060_38 c2_depth c2_kind c2_sign r0_level)))
theorem normalization_5801 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1682 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1710 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair060_42 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_41 c2_depth c2_kind c2_sign r0_group r0_level)) := (iff_congr (normalization_5662 c2_depth c2_kind c2_sign r0_group r0_level) (normalization_5800 c2_depth c2_kind c2_sign r0_group r0_level))

-- Checked replay of monotonicity.
theorem replay_3517 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1682 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1710 c2_depth c2_kind c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1454 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (shared_expr_Repair060_38 c2_depth c2_kind c2_sign r0_level) (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1766 r0_group) (replay_352 r0_group)
  have n1 : ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3077 c2_kind) (replay_2157 c2_kind)
  have n2 : ((shared_expr_Repair060_38 c2_depth c2_kind c2_sign r0_level) ↔ (¬ (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))) := by
    exact Iff.mp (normalization_5799 c2_depth c2_kind c2_sign r0_level) (replay_3516 c2_depth c2_kind c2_sign r0_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5801 c2_depth c2_kind c2_sign r0_group r0_level) hn

theorem normalized_1455 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair060_43 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
theorem normalization_5802 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level) := (or_congr (and_congr (normalization_1763 r0_group) (normalization_5797 c2_depth c2_kind c2_sign r0_level)) (and_congr (not_congr (normalization_1763 r0_group)) (normalization_1076 c2_kind)))

theorem normalization_5803 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1710 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair060_41 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level)) := (iff_congr (normalization_5800 c2_depth c2_kind c2_sign r0_group r0_level) (normalization_5802 c2_depth c2_kind c2_sign r0_group r0_level))

-- Checked replay of rewrite.
theorem replay_3518 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1710 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1455 ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (shared_expr_Repair060_39 c2_depth c2_kind c2_sign r0_level))
  have hn := ht
  exact Iff.mpr (normalization_5803 c2_depth c2_kind c2_sign r0_group r0_level) hn

theorem normalized_1456 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5804 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1682 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((shared_expr_Repair060_42 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level)) := (iff_congr (normalization_5662 c2_depth c2_kind c2_sign r0_group r0_level) (normalization_5802 c2_depth c2_kind c2_sign r0_group r0_level))

-- Checked replay of trans.
theorem replay_3519 (c2_depth c2_kind c2_sign r0_group r0_level : Int) : ((formula_1682 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_1456 (shared_expr_Repair060_42 c2_depth c2_kind c2_sign r0_group r0_level) (shared_expr_Repair060_41 c2_depth c2_kind c2_sign r0_group r0_level) (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level))
  have n0 : ((shared_expr_Repair060_42 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_41 c2_depth c2_kind c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5801 c2_depth c2_kind c2_sign r0_group r0_level) (replay_3517 c2_depth c2_kind c2_sign r0_group r0_level)
  have n1 : ((shared_expr_Repair060_41 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5803 c2_depth c2_kind c2_sign r0_group r0_level) (replay_3518 c2_depth c2_kind c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5804 c2_depth c2_kind c2_sign r0_group r0_level) hn

abbrev shared_expr_Repair060_44 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (1 : Int)) ∧ (formula_1682 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))))) ∧ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)))
abbrev formula_1711 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair060_44 c2_depth c2_kind c2_sign r0_group r0_level r0_mode)

theorem normalized_1457 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5805 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : ((¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))))) ∧ (formula_1593 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level)) := (and_congr (normalization_1837 r0_mode) (normalization_5802 c2_depth c2_kind c2_sign r0_group r0_level))

abbrev shared_expr_Repair060_45 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair060_42 c2_depth c2_kind c2_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level)))
theorem normalization_5806 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1711 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair060_45 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := (iff_congr (normalization_5663 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) (normalization_5805 c2_depth c2_kind c2_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_3520 (c2_depth c2_kind c2_sign r0_group r0_level r0_mode : Int) : (formula_1711 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_1457 (((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))) (shared_expr_Repair060_42 c2_depth c2_kind c2_sign r0_group r0_level) (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level))
  have n0 : ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1839 r0_mode) (replay_374 r0_mode)
  have n1 : ((shared_expr_Repair060_42 c2_depth c2_kind c2_sign r0_group r0_level) ↔ (shared_expr_Repair060_43 c2_depth c2_kind c2_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_5804 c2_depth c2_kind c2_sign r0_group r0_level) (replay_3519 c2_depth c2_kind c2_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5806 c2_depth c2_kind c2_sign r0_group r0_level r0_mode) hn

end H4Formal.Generated.Repair
