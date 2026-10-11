import H4Formal.BooleanReplaySupport
import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair065

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_1560 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6211 (c1_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6212 (c1_mode r3_mode : Int) : ((r3_mode ≤ c1_mode) ↔ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ↔ ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_6207 c1_mode r3_mode) (normalization_6211 c1_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_3826 (c1_mode r3_mode : Int) : ((r3_mode ≤ c1_mode) ↔ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1560 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6212 c1_mode r3_mode) hn

theorem normalized_1561 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6213 (c1_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) ↔ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_6214 (c1_mode r3_mode : Int) : ((r3_mode ≥ c1_mode) ↔ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ (((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (iff_congr (normalization_6208 c1_mode r3_mode) (normalization_6213 c1_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_3827 (c1_mode r3_mode : Int) : ((r3_mode ≥ c1_mode) ↔ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1561 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6214 c1_mode r3_mode) hn

theorem normalized_1562 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6215 (c1_mode r3_mode : Int) : (((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_6211 c1_mode r3_mode) (normalization_6213 c1_mode r3_mode))

abbrev shared_expr_Repair066_0 (c1_mode r3_mode : Int) : Prop := (((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
theorem normalization_6216 (c1_mode r3_mode : Int) : (((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ (((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Repair066_0 c1_mode r3_mode) := (iff_congr (normalization_6209 c1_mode r3_mode) (normalization_6215 c1_mode r3_mode))

-- Checked replay of monotonicity.
theorem replay_3828 (c1_mode r3_mode : Int) : (((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ (((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1562 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6212 c1_mode r3_mode) (replay_3826 c1_mode r3_mode)
  have n1 : (((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6214 c1_mode r3_mode) (replay_3827 c1_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6216 c1_mode r3_mode) hn

abbrev shared_expr_Repair066_1 (c1_mode r3_mode : Int) : Prop := ((((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))))
abbrev formula_1860 (c1_mode r3_mode : Int) : Prop := (shared_expr_Repair066_1 c1_mode r3_mode)

theorem normalized_1563 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6217 (c1_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_6211 c1_mode r3_mode))

theorem normalization_6218 (c1_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (not_congr (normalization_6213 c1_mode r3_mode))

theorem normalization_6219 (c1_mode r3_mode : Int) : ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) := (or_congr (normalization_6217 c1_mode r3_mode) (normalization_6218 c1_mode r3_mode))

theorem normalization_6220 (c1_mode r3_mode : Int) : (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) := (not_congr (normalization_6219 c1_mode r3_mode))

abbrev shared_expr_Repair066_2 (c1_mode r3_mode : Int) : Prop := (((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))))
theorem normalization_6221 (c1_mode r3_mode : Int) : (formula_1860 c1_mode r3_mode) ↔ (shared_expr_Repair066_2 c1_mode r3_mode) := (iff_congr (normalization_6215 c1_mode r3_mode) (normalization_6220 c1_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_3829 (c1_mode r3_mode : Int) : (formula_1860 c1_mode r3_mode) := by
  classical
  have ht := (normalized_1563 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6221 c1_mode r3_mode) hn

theorem normalized_1564 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6222 (c1_mode r3_mode : Int) : (((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair066_2 c1_mode r3_mode) := (iff_congr (normalization_6209 c1_mode r3_mode) (normalization_6220 c1_mode r3_mode))

-- Checked replay of trans.
theorem replay_3830 (c1_mode r3_mode : Int) : (((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1564 ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Repair066_2 c1_mode r3_mode))
  have n0 : (shared_expr_Repair066_0 c1_mode r3_mode) := by
    exact Iff.mp (normalization_6216 c1_mode r3_mode) (replay_3828 c1_mode r3_mode)
  have n1 : (shared_expr_Repair066_2 c1_mode r3_mode) := by
    exact Iff.mp (normalization_6221 c1_mode r3_mode) (replay_3829 c1_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6222 c1_mode r3_mode) hn

theorem normalized_1565 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6223 (c1_mode r3_mode : Int) : ((r3_mode = c1_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair066_2 c1_mode r3_mode) := (iff_congr (normalization_6020 c1_mode r3_mode) (normalization_6220 c1_mode r3_mode))

-- Checked replay of trans.
theorem replay_3831 (c1_mode r3_mode : Int) : ((r3_mode = c1_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1565 ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Repair066_2 c1_mode r3_mode))
  have n0 : (shared_expr_Repair066_0 c1_mode r3_mode) := by
    exact Iff.mp (normalization_6210 c1_mode r3_mode) (replay_3825 c1_mode r3_mode)
  have n1 : (shared_expr_Repair066_2 c1_mode r3_mode) := by
    exact Iff.mp (normalization_6222 c1_mode r3_mode) (replay_3830 c1_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6223 c1_mode r3_mode) hn

theorem normalized_1566 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6224 (c1_level r3_level : Int) : (r3_level ≤ c1_level) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6225 (c1_level r3_level : Int) : (r3_level ≥ c1_level) ↔ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_6226 (c1_level r3_level : Int) : ((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_6224 c1_level r3_level) (normalization_6225 c1_level r3_level))

abbrev shared_expr_Repair066_3 (c1_level r3_level : Int) : Prop := (((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
theorem normalization_6227 (c1_level r3_level : Int) : ((r3_level = c1_level) ↔ ((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level))) ↔ (shared_expr_Repair066_3 c1_level r3_level) := (iff_congr (normalization_6021 c1_level r3_level) (normalization_6226 c1_level r3_level))

-- Checked replay of rewrite.
theorem replay_3832 (c1_level r3_level : Int) : ((r3_level = c1_level) ↔ ((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level))) := by
  classical
  have ht := (normalized_1566 ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6227 c1_level r3_level) hn

theorem normalized_1567 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6228 (c1_level r3_level : Int) : ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6229 (c1_level r3_level : Int) : ((r3_level ≤ c1_level) ↔ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_6224 c1_level r3_level) (normalization_6228 c1_level r3_level))

-- Checked replay of rewrite.
theorem replay_3833 (c1_level r3_level : Int) : ((r3_level ≤ c1_level) ↔ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1567 ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6229 c1_level r3_level) hn

theorem normalized_1568 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6230 (c1_level r3_level : Int) : ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_6231 (c1_level r3_level : Int) : ((r3_level ≥ c1_level) ↔ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (iff_congr (normalization_6225 c1_level r3_level) (normalization_6230 c1_level r3_level))

-- Checked replay of rewrite.
theorem replay_3834 (c1_level r3_level : Int) : ((r3_level ≥ c1_level) ↔ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1568 ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6231 c1_level r3_level) hn

theorem normalized_1569 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6232 (c1_level r3_level : Int) : (((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_6228 c1_level r3_level) (normalization_6230 c1_level r3_level))

theorem normalization_6233 (c1_level r3_level : Int) : (((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ (((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ↔ (shared_expr_Repair066_3 c1_level r3_level) := (iff_congr (normalization_6226 c1_level r3_level) (normalization_6232 c1_level r3_level))

-- Checked replay of monotonicity.
theorem replay_3835 (c1_level r3_level : Int) : (((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ (((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1569 ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6229 c1_level r3_level) (replay_3833 c1_level r3_level)
  have n1 : (((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6231 c1_level r3_level) (replay_3834 c1_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6233 c1_level r3_level) hn

abbrev shared_expr_Repair066_4 (c1_level r3_level : Int) : Prop := ((((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))))
abbrev formula_1861 (c1_level r3_level : Int) : Prop := (shared_expr_Repair066_4 c1_level r3_level)

theorem normalized_1570 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6234 (c1_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_6228 c1_level r3_level))

theorem normalization_6235 (c1_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_6230 c1_level r3_level))

theorem normalization_6236 (c1_level r3_level : Int) : ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) := (or_congr (normalization_6234 c1_level r3_level) (normalization_6235 c1_level r3_level))

theorem normalization_6237 (c1_level r3_level : Int) : (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) := (not_congr (normalization_6236 c1_level r3_level))

abbrev shared_expr_Repair066_5 (c1_level r3_level : Int) : Prop := (((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))))
theorem normalization_6238 (c1_level r3_level : Int) : (formula_1861 c1_level r3_level) ↔ (shared_expr_Repair066_5 c1_level r3_level) := (iff_congr (normalization_6232 c1_level r3_level) (normalization_6237 c1_level r3_level))

-- Checked replay of rewrite.
theorem replay_3836 (c1_level r3_level : Int) : (formula_1861 c1_level r3_level) := by
  classical
  have ht := (normalized_1570 ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6238 c1_level r3_level) hn

theorem normalized_1571 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6239 (c1_level r3_level : Int) : (((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair066_5 c1_level r3_level) := (iff_congr (normalization_6226 c1_level r3_level) (normalization_6237 c1_level r3_level))

-- Checked replay of trans.
theorem replay_3837 (c1_level r3_level : Int) : (((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1571 ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Repair066_5 c1_level r3_level))
  have n0 : (shared_expr_Repair066_3 c1_level r3_level) := by
    exact Iff.mp (normalization_6233 c1_level r3_level) (replay_3835 c1_level r3_level)
  have n1 : (shared_expr_Repair066_5 c1_level r3_level) := by
    exact Iff.mp (normalization_6238 c1_level r3_level) (replay_3836 c1_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6239 c1_level r3_level) hn

theorem normalized_1572 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6240 (c1_level r3_level : Int) : ((r3_level = c1_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair066_5 c1_level r3_level) := (iff_congr (normalization_6021 c1_level r3_level) (normalization_6237 c1_level r3_level))

-- Checked replay of trans.
theorem replay_3838 (c1_level r3_level : Int) : ((r3_level = c1_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1572 ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Repair066_5 c1_level r3_level))
  have n0 : (shared_expr_Repair066_3 c1_level r3_level) := by
    exact Iff.mp (normalization_6227 c1_level r3_level) (replay_3832 c1_level r3_level)
  have n1 : (shared_expr_Repair066_5 c1_level r3_level) := by
    exact Iff.mp (normalization_6239 c1_level r3_level) (replay_3837 c1_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6240 c1_level r3_level) hn

theorem normalized_1573 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6241 (c1_group r3_group : Int) : (r3_group ≤ c1_group) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6242 (c1_group r3_group : Int) : (r3_group ≥ c1_group) ↔ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_6243 (c1_group r3_group : Int) : ((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_6241 c1_group r3_group) (normalization_6242 c1_group r3_group))

abbrev shared_expr_Repair066_6 (c1_group r3_group : Int) : Prop := (((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
theorem normalization_6244 (c1_group r3_group : Int) : ((r3_group = c1_group) ↔ ((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group))) ↔ (shared_expr_Repair066_6 c1_group r3_group) := (iff_congr (normalization_6093 c1_group r3_group) (normalization_6243 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_3839 (c1_group r3_group : Int) : ((r3_group = c1_group) ↔ ((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group))) := by
  classical
  have ht := (normalized_1573 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6244 c1_group r3_group) hn

theorem normalized_1574 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6245 (c1_group r3_group : Int) : ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6246 (c1_group r3_group : Int) : ((r3_group ≤ c1_group) ↔ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ↔ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_6241 c1_group r3_group) (normalization_6245 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_3840 (c1_group r3_group : Int) : ((r3_group ≤ c1_group) ↔ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1574 ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6246 c1_group r3_group) hn

theorem normalized_1575 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6247 (c1_group r3_group : Int) : ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)) ↔ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_6248 (c1_group r3_group : Int) : ((r3_group ≥ c1_group) ↔ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ (((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (iff_congr (normalization_6242 c1_group r3_group) (normalization_6247 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_3841 (c1_group r3_group : Int) : ((r3_group ≥ c1_group) ↔ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1575 ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6248 c1_group r3_group) hn

theorem normalized_1576 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6249 (c1_group r3_group : Int) : (((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_6245 c1_group r3_group) (normalization_6247 c1_group r3_group))

theorem normalization_6250 (c1_group r3_group : Int) : (((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ (((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) ↔ (shared_expr_Repair066_6 c1_group r3_group) := (iff_congr (normalization_6243 c1_group r3_group) (normalization_6249 c1_group r3_group))

-- Checked replay of monotonicity.
theorem replay_3842 (c1_group r3_group : Int) : (((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ (((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1576 ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6246 c1_group r3_group) (replay_3840 c1_group r3_group)
  have n1 : (((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6248 c1_group r3_group) (replay_3841 c1_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6250 c1_group r3_group) hn

abbrev shared_expr_Repair066_7 (c1_group r3_group : Int) : Prop := ((((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))))
abbrev formula_1862 (c1_group r3_group : Int) : Prop := (shared_expr_Repair066_7 c1_group r3_group)

theorem normalized_1577 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6251 (c1_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_6245 c1_group r3_group))

theorem normalization_6252 (c1_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (not_congr (normalization_6247 c1_group r3_group))

theorem normalization_6253 (c1_group r3_group : Int) : ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) := (or_congr (normalization_6251 c1_group r3_group) (normalization_6252 c1_group r3_group))

theorem normalization_6254 (c1_group r3_group : Int) : (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))) := (not_congr (normalization_6253 c1_group r3_group))

abbrev shared_expr_Repair066_8 (c1_group r3_group : Int) : Prop := (((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_6255 (c1_group r3_group : Int) : (formula_1862 c1_group r3_group) ↔ (shared_expr_Repair066_8 c1_group r3_group) := (iff_congr (normalization_6249 c1_group r3_group) (normalization_6254 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_3843 (c1_group r3_group : Int) : (formula_1862 c1_group r3_group) := by
  classical
  have ht := (normalized_1577 ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6255 c1_group r3_group) hn

theorem normalized_1578 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6256 (c1_group r3_group : Int) : (((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair066_8 c1_group r3_group) := (iff_congr (normalization_6243 c1_group r3_group) (normalization_6254 c1_group r3_group))

-- Checked replay of trans.
theorem replay_3844 (c1_group r3_group : Int) : (((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1578 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Repair066_8 c1_group r3_group))
  have n0 : (shared_expr_Repair066_6 c1_group r3_group) := by
    exact Iff.mp (normalization_6250 c1_group r3_group) (replay_3842 c1_group r3_group)
  have n1 : (shared_expr_Repair066_8 c1_group r3_group) := by
    exact Iff.mp (normalization_6255 c1_group r3_group) (replay_3843 c1_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6256 c1_group r3_group) hn

theorem normalized_1579 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6257 (c1_group r3_group : Int) : ((r3_group = c1_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair066_8 c1_group r3_group) := (iff_congr (normalization_6093 c1_group r3_group) (normalization_6254 c1_group r3_group))

-- Checked replay of trans.
theorem replay_3845 (c1_group r3_group : Int) : ((r3_group = c1_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1579 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Repair066_8 c1_group r3_group))
  have n0 : (shared_expr_Repair066_6 c1_group r3_group) := by
    exact Iff.mp (normalization_6244 c1_group r3_group) (replay_3839 c1_group r3_group)
  have n1 : (shared_expr_Repair066_8 c1_group r3_group) := by
    exact Iff.mp (normalization_6256 c1_group r3_group) (replay_3844 c1_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6257 c1_group r3_group) hn

theorem normalized_1580 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6258 (c1_group r3_group : Int) : (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) := (not_congr (normalization_6254 c1_group r3_group))

abbrev shared_expr_Repair066_9 (c1_group r3_group : Int) : Prop := ((¬ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))))
theorem normalization_6259 (c1_group r3_group : Int) : ((¬ (r3_group = c1_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Repair066_9 c1_group r3_group) := (iff_congr (normalization_6094 c1_group r3_group) (normalization_6258 c1_group r3_group))

-- Checked replay of monotonicity.
theorem replay_3846 (c1_group r3_group : Int) : ((¬ (r3_group = c1_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1580 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair066_8 c1_group r3_group) := by
    exact Iff.mp (normalization_6257 c1_group r3_group) (replay_3845 c1_group r3_group)
  have hn := ht n0
  exact Iff.mpr (normalization_6259 c1_group r3_group) hn

abbrev shared_expr_Repair066_10 (c1_group r3_group : Int) : Prop := ((¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))
abbrev formula_1863 (c1_group r3_group : Int) : Prop := (shared_expr_Repair066_10 c1_group r3_group)

theorem normalized_1581 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair066_11 (c1_group r3_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_6260 (c1_group r3_group : Int) : (formula_1863 c1_group r3_group) ↔ (shared_expr_Repair066_11 c1_group r3_group) := (iff_congr (normalization_6258 c1_group r3_group) (normalization_6253 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_3847 (c1_group r3_group : Int) : (formula_1863 c1_group r3_group) := by
  classical
  have ht := (normalized_1581 ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6260 c1_group r3_group) hn

theorem normalized_1582 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair066_12 (c1_group r3_group : Int) : Prop := ((¬ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_6261 (c1_group r3_group : Int) : ((¬ (r3_group = c1_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))) ↔ (shared_expr_Repair066_12 c1_group r3_group) := (iff_congr (normalization_6094 c1_group r3_group) (normalization_6253 c1_group r3_group))

-- Checked replay of trans.
theorem replay_3848 (c1_group r3_group : Int) : ((¬ (r3_group = c1_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1582 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair066_9 c1_group r3_group) := by
    exact Iff.mp (normalization_6259 c1_group r3_group) (replay_3846 c1_group r3_group)
  have n1 : (shared_expr_Repair066_11 c1_group r3_group) := by
    exact Iff.mp (normalization_6260 c1_group r3_group) (replay_3847 c1_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6261 c1_group r3_group) hn

abbrev shared_expr_Repair066_13 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))) ∧ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))
abbrev formula_1864 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair066_13 c1_group c1_level c1_mode r3_group r3_level r3_mode)

theorem normalized_1583 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair066_14 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_6262 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (formula_1864 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_14 c1_group c1_level c1_mode r3_group r3_level r3_mode) := (and_congr (normalization_6220 c1_mode r3_mode) (and_congr (normalization_6237 c1_level r3_level) (normalization_6253 c1_group r3_group)))

abbrev shared_expr_Repair066_15 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := (((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_6263 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group))) ↔ (formula_1864 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ↔ ((shared_expr_Repair066_15 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_14 c1_group c1_level c1_mode r3_group r3_level r3_mode)) := (iff_congr (normalization_6095 c1_group c1_level c1_mode r3_group r3_level r3_mode) (normalization_6262 c1_group c1_level c1_mode r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_3849 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group))) ↔ (formula_1864 c1_group c1_level c1_mode r3_group r3_level r3_mode)) := by
  classical
  have ht := (normalized_1583 ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair066_2 c1_mode r3_mode) := by
    exact Iff.mp (normalization_6223 c1_mode r3_mode) (replay_3831 c1_mode r3_mode)
  have n1 : (shared_expr_Repair066_5 c1_level r3_level) := by
    exact Iff.mp (normalization_6240 c1_level r3_level) (replay_3838 c1_level r3_level)
  have n2 : (shared_expr_Repair066_12 c1_group r3_group) := by
    exact Iff.mp (normalization_6261 c1_group r3_group) (replay_3848 c1_group r3_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6263 c1_group c1_level c1_mode r3_group r3_level r3_mode) hn

theorem normalized_1584 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair066_16 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_6264 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (formula_1793 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode) := (or_congr (normalization_6217 c1_mode r3_mode) (or_congr (normalization_6218 c1_mode r3_mode) (or_congr (normalization_6234 c1_level r3_level) (or_congr (normalization_6235 c1_level r3_level) (normalization_6254 c1_group r3_group)))))

theorem normalization_6265 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (¬ (formula_1793 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ↔ (¬ (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode)) := (not_congr (normalization_6264 c1_group c1_level c1_mode r3_group r3_level r3_mode))

theorem normalization_6266 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : ((formula_1864 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (formula_1793 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Repair066_14 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_6262 c1_group c1_level c1_mode r3_group r3_level r3_mode) (normalization_6265 c1_group c1_level c1_mode r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_3850 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : ((formula_1864 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (formula_1793 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_1584 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6266 c1_group c1_level c1_mode r3_group r3_level r3_mode) hn

theorem normalized_1585 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6267 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group))) ↔ (¬ (formula_1793 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Repair066_15 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_6095 c1_group c1_level c1_mode r3_group r3_level r3_mode) (normalization_6265 c1_group c1_level c1_mode r3_group r3_level r3_mode))

-- Checked replay of trans.
theorem replay_3851 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group))) ↔ (¬ (formula_1793 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_1585 (shared_expr_Repair066_15 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Repair066_14 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode))
  have n0 : ((shared_expr_Repair066_15 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_14 c1_group c1_level c1_mode r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_6263 c1_group c1_level c1_mode r3_group r3_level r3_mode) (replay_3849 c1_group c1_level c1_mode r3_group r3_level r3_mode)
  have n1 : ((shared_expr_Repair066_14 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_6266 c1_group c1_level c1_mode r3_group r3_level r3_mode) (replay_3850 c1_group c1_level c1_mode r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6267 c1_group c1_level c1_mode r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_3852 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((formula_1849 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1792 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) := by
  classical
  first
  | (simp only [formula_1849, shared_expr_Repair065_131, formula_1843, shared_expr_Repair065_125, formula_1844, shared_expr_Repair065_126, formula_1845, shared_expr_Repair065_127, formula_1846, shared_expr_Repair065_128, formula_1847, shared_expr_Repair065_129, formula_1848, shared_expr_Repair065_130, formula_1792, shared_expr_Repair064_16, formula_1781, shared_expr_Repair064_5, formula_1780, shared_expr_Repair064_4, formula_1783, shared_expr_Repair064_7, formula_1782, shared_expr_Repair064_6, formula_1785, shared_expr_Repair064_9, formula_1784, shared_expr_Repair064_8, formula_1787, shared_expr_Repair064_11, formula_1786, shared_expr_Repair064_10, formula_1789, shared_expr_Repair064_13, formula_1788, shared_expr_Repair064_12, formula_1791, shared_expr_Repair064_15, formula_1790, shared_expr_Repair064_14, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Repair066_17 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∧ (¬ (formula_1793 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ∧ (formula_1792 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
abbrev formula_1865 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair066_17 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

abbrev shared_expr_Repair066_18 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_1850 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1865 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
abbrev formula_1866 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair066_18 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

theorem normalized_1586 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6268 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_6269 (c1_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) := (not_congr (normalization_6268 c1_depth r3_level))

theorem normalization_6270 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_6271 (c1_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := (not_congr (normalization_6270 c1_depth r3_level))

abbrev shared_expr_Repair066_19 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_6272 (c1_depth c1_kind c1_sign r3_level : Int) : (formula_1780 c1_depth c1_kind c1_sign r3_level) ↔ (shared_expr_Repair066_19 c1_depth c1_kind c1_sign r3_level) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1813 c1_sign) (or_congr (normalization_6269 c1_depth r3_level) (normalization_6271 c1_depth r3_level)))))

theorem normalization_6273 (c1_depth c1_kind c1_sign r3_level : Int) : (¬ (formula_1780 c1_depth c1_kind c1_sign r3_level)) ↔ (¬ (shared_expr_Repair066_19 c1_depth c1_kind c1_sign r3_level)) := (not_congr (normalization_6272 c1_depth c1_kind c1_sign r3_level))

abbrev shared_expr_Repair066_20 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair066_19 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
theorem normalization_6274 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (formula_1781 c1_depth c1_kind c1_sign r3_group r3_level) ↔ (shared_expr_Repair066_20 c1_depth c1_kind c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_6273 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_1774 c1_kind)))

theorem normalization_6275 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (¬ (formula_1781 c1_depth c1_kind c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair066_20 c1_depth c1_kind c1_sign r3_group r3_level)) := (not_congr (normalization_6274 c1_depth c1_kind c1_sign r3_group r3_level))

theorem normalization_6276 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_1781 c1_depth c1_kind c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair066_20 c1_depth c1_kind c1_sign r3_group r3_level))) := (or_congr (normalization_2690 r3_mode) (or_congr (normalization_2691 r3_mode) (normalization_6275 c1_depth c1_kind c1_sign r3_group r3_level)))

theorem normalization_6277 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_1781 c1_depth c1_kind c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair066_20 c1_depth c1_kind c1_sign r3_group r3_level)))) := (not_congr (normalization_6276 c1_depth c1_kind c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair066_21 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_6278 (c1_depth c1_kind c1_sign r3_level : Int) : (formula_1782 c1_depth c1_kind c1_sign r3_level) ↔ (shared_expr_Repair066_21 c1_depth c1_kind c1_sign r3_level) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1850 c1_sign) (or_congr (normalization_6269 c1_depth r3_level) (normalization_6271 c1_depth r3_level)))))

theorem normalization_6279 (c1_depth c1_kind c1_sign r3_level : Int) : (¬ (formula_1782 c1_depth c1_kind c1_sign r3_level)) ↔ (¬ (shared_expr_Repair066_21 c1_depth c1_kind c1_sign r3_level)) := (not_congr (normalization_6278 c1_depth c1_kind c1_sign r3_level))

abbrev shared_expr_Repair066_22 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair066_21 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
theorem normalization_6280 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (formula_1783 c1_depth c1_kind c1_sign r3_group r3_level) ↔ (shared_expr_Repair066_22 c1_depth c1_kind c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_6279 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_1774 c1_kind)))

theorem normalization_6281 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (¬ (formula_1783 c1_depth c1_kind c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair066_22 c1_depth c1_kind c1_sign r3_group r3_level)) := (not_congr (normalization_6280 c1_depth c1_kind c1_sign r3_group r3_level))

theorem normalization_6282 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_1783 c1_depth c1_kind c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair066_22 c1_depth c1_kind c1_sign r3_group r3_level))) := (or_congr (normalization_4616 r3_mode) (or_congr (normalization_4618 r3_mode) (normalization_6281 c1_depth c1_kind c1_sign r3_group r3_level)))

theorem normalization_6283 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_1783 c1_depth c1_kind c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair066_22 c1_depth c1_kind c1_sign r3_group r3_level)))) := (not_congr (normalization_6282 c1_depth c1_kind c1_sign r3_group r3_level r3_mode))

theorem normalization_6284 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_6285 (c1_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_6284 c1_depth r3_level))

theorem normalization_6286 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6287 (c1_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_6286 c1_depth r3_level))

abbrev shared_expr_Repair066_23 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_6288 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (formula_1784 c1_depth c1_kind c1_node c1_sign r3_level) ↔ (shared_expr_Repair066_23 c1_depth c1_kind c1_node c1_sign r3_level) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1813 c1_sign) (or_congr (normalization_1906 c1_node) (or_congr (normalization_6285 c1_depth r3_level) (normalization_6287 c1_depth r3_level))))))

theorem normalization_6289 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (¬ (formula_1784 c1_depth c1_kind c1_node c1_sign r3_level)) ↔ (¬ (shared_expr_Repair066_23 c1_depth c1_kind c1_node c1_sign r3_level)) := (not_congr (normalization_6288 c1_depth c1_kind c1_node c1_sign r3_level))

abbrev shared_expr_Repair066_24 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair066_23 c1_depth c1_kind c1_node c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_19 c1_depth c1_kind c1_sign r3_level))))
theorem normalization_6290 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1785 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Repair066_24 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_6289 c1_depth c1_kind c1_node c1_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_6273 c1_depth c1_kind c1_sign r3_level)))

theorem normalization_6291 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (¬ (formula_1785 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair066_24 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (not_congr (normalization_6290 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

theorem normalization_6292 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_1785 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair066_24 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) := (or_congr (normalization_4626 r3_mode) (or_congr (normalization_4628 r3_mode) (normalization_6291 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))

theorem normalization_6293 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_1785 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair066_24 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) := (not_congr (normalization_6292 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair066_25 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_6294 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (formula_1786 c1_depth c1_kind c1_node c1_sign r3_level) ↔ (shared_expr_Repair066_25 c1_depth c1_kind c1_node c1_sign r3_level) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1813 c1_sign) (or_congr (normalization_1945 c1_node) (or_congr (normalization_6285 c1_depth r3_level) (normalization_6287 c1_depth r3_level))))))

theorem normalization_6295 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (¬ (formula_1786 c1_depth c1_kind c1_node c1_sign r3_level)) ↔ (¬ (shared_expr_Repair066_25 c1_depth c1_kind c1_node c1_sign r3_level)) := (not_congr (normalization_6294 c1_depth c1_kind c1_node c1_sign r3_level))

abbrev shared_expr_Repair066_26 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair066_25 c1_depth c1_kind c1_node c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_19 c1_depth c1_kind c1_sign r3_level))))
theorem normalization_6296 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1787 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Repair066_26 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_6295 c1_depth c1_kind c1_node c1_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_6273 c1_depth c1_kind c1_sign r3_level)))

theorem normalization_6297 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (¬ (formula_1787 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair066_26 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (not_congr (normalization_6296 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

theorem normalization_6298 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_1787 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair066_26 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) := (or_congr (normalization_4640 r3_mode) (or_congr (normalization_4642 r3_mode) (normalization_6297 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))

theorem normalization_6299 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_1787 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair066_26 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) := (not_congr (normalization_6298 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair066_27 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_6300 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (formula_1788 c1_depth c1_kind c1_node c1_sign r3_level) ↔ (shared_expr_Repair066_27 c1_depth c1_kind c1_node c1_sign r3_level) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1850 c1_sign) (or_congr (normalization_1906 c1_node) (or_congr (normalization_6285 c1_depth r3_level) (normalization_6287 c1_depth r3_level))))))

theorem normalization_6301 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (¬ (formula_1788 c1_depth c1_kind c1_node c1_sign r3_level)) ↔ (¬ (shared_expr_Repair066_27 c1_depth c1_kind c1_node c1_sign r3_level)) := (not_congr (normalization_6300 c1_depth c1_kind c1_node c1_sign r3_level))

abbrev shared_expr_Repair066_28 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair066_21 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_27 c1_depth c1_kind c1_node c1_sign r3_level))))
theorem normalization_6302 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1789 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Repair066_28 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_6279 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_6301 c1_depth c1_kind c1_node c1_sign r3_level)))

theorem normalization_6303 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (¬ (formula_1789 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair066_28 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (not_congr (normalization_6302 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

theorem normalization_6304 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_1789 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair066_28 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) := (or_congr (normalization_4650 r3_mode) (or_congr (normalization_4651 r3_mode) (normalization_6303 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))

theorem normalization_6305 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_1789 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair066_28 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) := (not_congr (normalization_6304 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair066_29 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_6306 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (formula_1790 c1_depth c1_kind c1_node c1_sign r3_level) ↔ (shared_expr_Repair066_29 c1_depth c1_kind c1_node c1_sign r3_level) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1850 c1_sign) (or_congr (normalization_1945 c1_node) (or_congr (normalization_6285 c1_depth r3_level) (normalization_6287 c1_depth r3_level))))))

theorem normalization_6307 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (¬ (formula_1790 c1_depth c1_kind c1_node c1_sign r3_level)) ↔ (¬ (shared_expr_Repair066_29 c1_depth c1_kind c1_node c1_sign r3_level)) := (not_congr (normalization_6306 c1_depth c1_kind c1_node c1_sign r3_level))

abbrev shared_expr_Repair066_30 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair066_21 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_29 c1_depth c1_kind c1_node c1_sign r3_level))))
theorem normalization_6308 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1791 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Repair066_30 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_6279 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_6307 c1_depth c1_kind c1_node c1_sign r3_level)))

theorem normalization_6309 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (¬ (formula_1791 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair066_30 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (not_congr (normalization_6308 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

theorem normalization_6310 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_1791 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair066_30 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) := (or_congr (normalization_4659 r3_mode) (or_congr (normalization_4661 r3_mode) (normalization_6309 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))

theorem normalization_6311 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_1791 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair066_30 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) := (not_congr (normalization_6310 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair066_31 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair066_20 c1_depth c1_kind c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair066_22 c1_depth c1_kind c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair066_24 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair066_26 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair066_28 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair066_30 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))))
theorem normalization_6312 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1792 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_31 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) := (or_congr (normalization_6277 c1_depth c1_kind c1_sign r3_group r3_level r3_mode) (or_congr (normalization_6283 c1_depth c1_kind c1_sign r3_group r3_level r3_mode) (or_congr (normalization_6293 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (or_congr (normalization_6299 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (or_congr (normalization_6305 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (normalization_6311 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))))))

abbrev shared_expr_Repair066_32 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_33 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair066_32 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Repair066_34 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_35 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair066_34 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Repair066_36 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair066_37 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_32 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair066_36 c1_depth c1_kind c1_node c1_sign r3_level)))
abbrev shared_expr_Repair066_38 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair066_39 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_32 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair066_38 c1_depth c1_kind c1_node c1_sign r3_level)))
abbrev shared_expr_Repair066_40 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair066_41 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_40 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair066_34 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Repair066_42 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair066_43 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_42 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair066_34 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Repair066_44 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair066_33 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_35 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair066_37 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair066_39 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair066_41 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair066_43 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))
theorem normalization_6313 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((formula_1849 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1792 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) ↔ ((shared_expr_Repair066_44 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_31 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) := (iff_congr (normalization_6176 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (normalization_6312 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair066_45 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair066_31 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
theorem normalization_6314 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1865 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_45 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_1683 c1_kind) (normalization_6265 c1_group c1_level c1_mode r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_1683 c1_kind)) (normalization_6312 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))

abbrev shared_expr_Repair066_46 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair066_15 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair066_44 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Repair066_47 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Repair066_46 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_45 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
theorem normalization_6315 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1866 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_47 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (iff_congr (normalization_6177 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (normalization_6314 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_3853 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1866 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_1586 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Repair066_15 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Repair066_44 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (shared_expr_Repair066_31 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1685 c1_kind) (replay_319 c1_kind)
  have n1 : ((shared_expr_Repair066_15 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_6267 c1_group c1_level c1_mode r3_group r3_level r3_mode) (replay_3851 c1_group c1_level c1_mode r3_group r3_level r3_mode)
  have n2 : ((shared_expr_Repair066_44 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_31 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_6313 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (replay_3852 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6315 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) hn

abbrev shared_expr_Repair066_48 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_1865 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1794 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
abbrev formula_1867 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair066_48 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

theorem normalized_1587 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair066_49 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair066_31 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) ∨ ((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode))))
theorem normalization_6316 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1794 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_1682 c1_kind) (normalization_6312 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_1682 c1_kind)) (normalization_6265 c1_group c1_level c1_mode r3_group r3_level r3_mode)))

abbrev shared_expr_Repair066_50 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Repair066_45 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
theorem normalization_6317 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1867 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_50 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (iff_congr (normalization_6314 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (normalization_6316 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_3854 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1867 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_1587 ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Repair066_16 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Repair066_31 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))
  have hn := ht
  exact Iff.mpr (normalization_6317 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) hn

abbrev shared_expr_Repair066_51 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_1850 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1794 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
abbrev formula_1868 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair066_51 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

theorem normalized_1588 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair066_52 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Repair066_46 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
theorem normalization_6318 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1868 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair066_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (iff_congr (normalization_6177 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (normalization_6316 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))

-- Checked replay of trans.
theorem replay_3855 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1868 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_1588 (shared_expr_Repair066_46 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (shared_expr_Repair066_45 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (shared_expr_Repair066_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
  have n0 : (shared_expr_Repair066_47 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_6315 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (replay_3853 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)
  have n1 : (shared_expr_Repair066_50 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_6317 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (replay_3854 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6318 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_3856 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1853 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (formula_1761 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) := by
  classical
  first
  | (simp only [formula_1853, shared_expr_Repair065_135, formula_1851, shared_expr_Repair065_133, formula_1852, shared_expr_Repair065_134, formula_1827, shared_expr_Repair065_31, formula_1828, shared_expr_Repair065_32, formula_1829, shared_expr_Repair065_33, formula_1830, shared_expr_Repair065_34, formula_1761, shared_expr_Repair063_14, formula_1752, shared_expr_Repair063_5, formula_1750, shared_expr_Repair063_3, formula_1751, shared_expr_Repair063_4, formula_1749, shared_expr_Repair063_2, formula_1748, shared_expr_Repair063_1, formula_1747, shared_expr_Repair063_0, formula_1754, shared_expr_Repair063_7, formula_1753, shared_expr_Repair063_6, formula_1756, shared_expr_Repair063_9, formula_1755, shared_expr_Repair063_8, formula_1758, shared_expr_Repair063_11, formula_1757, shared_expr_Repair063_10, formula_1760, shared_expr_Repair063_13, formula_1759, shared_expr_Repair063_12, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_1589 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : (((((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ∧ (¬ ((p0 ∧ (¬ p1)) ∧ (p3 ∧ (¬ p4)) ∧ (p5 ∧ (¬ p6))))) ∨ ((¬ ((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3)))) ∧ ((((¬ p7) ∧ p8) ∧ (((p9 ∧ (¬ p10)) ∧ (p11 ∧ (¬ p12)) ∧ (¬ p13)) ∨ ((p14 ∧ (¬ p15)) ∧ (p16 ∧ (¬ p17)) ∧ ((¬ p18) ∧ p19) ∧ (¬ p13)) ∨ ((p15 ∧ (¬ p9)) ∧ (p17 ∧ (¬ p11)) ∧ (¬ p19) ∧ (¬ p20)))) ∨ (((¬ p21) ∧ p7) ∧ ((((p9 ∧ (¬ p10)) ∨ (p14 ∧ (¬ p15))) ∧ (p11 ∧ (¬ p12)) ∧ p22) ∨ (((p15 ∧ (¬ p9)) ∨ (p14 ∧ (¬ p15))) ∧ (p17 ∧ (¬ p11)) ∧ (¬ (¬ p23)))))))) ↔ ((((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ∧ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p3) ∨ (¬ (¬ p4)) ∨ (¬ p5) ∨ (¬ (¬ p6)))) ∨ ((¬ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) ∧ ((¬ ((¬ (¬ p7)) ∨ (¬ p8) ∨ (¬ ((¬ ((¬ p9) ∨ (¬ (¬ p10)) ∨ (¬ p11) ∨ (¬ (¬ p12)) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p19) ∨ (¬ (¬ p18)) ∨ (¬ p14) ∨ (¬ (¬ p15)) ∨ (¬ p16) ∨ (¬ (¬ p17)) ∨ (¬ (¬ p13)))) ∨ (¬ (p19 ∨ p20 ∨ (¬ p15) ∨ (¬ (¬ p9)) ∨ (¬ p17) ∨ (¬ (¬ p11)))))))) ∨ (¬ ((¬ (¬ p21)) ∨ (¬ p7) ∨ (¬ ((¬ ((¬ p11) ∨ (¬ (¬ p12)) ∨ (¬ ((¬ ((¬ p9) ∨ (¬ (¬ p10)))) ∨ (¬ ((¬ p14) ∨ (¬ (¬ p15)))))) ∨ (¬ p22))) ∨ (¬ ((¬ p23) ∨ (¬ p17) ∨ (¬ (¬ p11)) ∨ (¬ ((¬ ((¬ p15) ∨ (¬ (¬ p9)))) ∨ (¬ ((¬ p14) ∨ (¬ (¬ p15)))))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6319 (c1_kind r3_kind : Int) : ((¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := (or_congr (normalization_1386 r3_kind) (normalization_1774 c1_kind))

abbrev shared_expr_Repair066_53 (c1_depth c1_kind h r3_kind : Int) : Prop := ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
theorem normalization_6320 (c1_depth c1_kind h r3_kind : Int) : (formula_1765 c1_depth c1_kind h r3_kind) ↔ (shared_expr_Repair066_53 c1_depth c1_kind h r3_kind) := (or_congr (normalization_1382 r3_kind) (or_congr (normalization_1384 r3_kind) (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_2034 c1_depth h) (normalization_2036 c1_depth h))))))

theorem normalization_6321 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6322 (c1_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_6321 c1_depth r3_depth))

theorem normalization_6323 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6324 (c1_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (not_congr (normalization_6323 c1_depth r3_depth))

theorem normalization_6325 (c1_node r3_node : Int) : (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6186 c1_node r3_node))

theorem normalization_6326 (c1_node c1_sign r3_node r3_sign : Int) : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ↔ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_1405 r3_sign) (or_congr (normalization_1407 r3_sign) (or_congr (normalization_1798 c1_sign) (or_congr (normalization_1800 c1_sign) (normalization_6325 c1_node r3_node)))))

theorem normalization_6327 (c1_node c1_sign r3_node r3_sign : Int) : (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_6326 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Repair066_54 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))) ∨ (¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))
theorem normalization_6328 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1766 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Repair066_54 c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2736 h r3_depth) (or_congr (normalization_2730 h r3_depth) (or_congr (normalization_2746 r3_sign) (or_congr (normalization_2748 r3_sign) (or_congr (normalization_1804 c1_sign) (or_congr (normalization_1806 c1_sign) (normalization_6325 c1_node r3_node)))))))

theorem normalization_6329 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_1766 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_54 c1_node c1_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_6328 c1_node c1_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Repair066_55 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ∨ ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ∨ (¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))
theorem normalization_6330 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1767 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Repair066_55 c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2735 h r3_depth) (or_congr (normalization_6189 c1_node r3_node) (or_congr (normalization_2739 r3_sign) (or_congr (normalization_2741 r3_sign) (or_congr (normalization_1841 c1_sign) (normalization_1843 c1_sign))))))

theorem normalization_6331 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_1767 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_55 c1_node c1_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_6330 c1_node c1_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Repair066_56 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair066_54 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ (shared_expr_Repair066_55 c1_node c1_sign h r3_depth r3_node r3_sign)))
theorem normalization_6332 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Repair066_56 c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_6327 c1_node c1_sign r3_node r3_sign) (or_congr (normalization_6329 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_6331 c1_node c1_sign h r3_depth r3_node r3_sign)))

theorem normalization_6333 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_56 c1_node c1_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_6332 c1_node c1_sign h r3_depth r3_node r3_sign))

theorem normalization_6334 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign))) ↔ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair066_56 c1_node c1_sign h r3_depth r3_node r3_sign))) := (or_congr (normalization_6322 c1_depth r3_depth) (or_congr (normalization_6324 c1_depth r3_depth) (normalization_6333 c1_node c1_sign h r3_depth r3_node r3_sign)))

theorem normalization_6335 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign)))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair066_56 c1_node c1_sign h r3_depth r3_node r3_sign)))) := (not_congr (normalization_6334 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))

theorem normalization_6336 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_6337 (c1_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_6336 c1_depth r3_depth))

theorem normalization_6338 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_6339 (c1_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := (not_congr (normalization_6338 c1_depth r3_depth))

theorem normalization_6340 (c1_node r3_node : Int) : (¬ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (not_congr (normalization_6195 c1_node r3_node))

abbrev shared_expr_Repair066_57 (c1_node c1_sign r3_node r3_sign : Int) : Prop := ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_6341 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1769 c1_node c1_sign r3_node r3_sign) ↔ (shared_expr_Repair066_57 c1_node c1_sign r3_node r3_sign) := (or_congr (normalization_1798 c1_sign) (or_congr (normalization_1800 c1_sign) (or_congr (normalization_4697 r3_sign) (normalization_6340 c1_node r3_node))))

theorem normalization_6342 (c1_node c1_sign r3_node r3_sign : Int) : (¬ (formula_1769 c1_node c1_sign r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_57 c1_node c1_sign r3_node r3_sign)) := (not_congr (normalization_6341 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Repair066_58 (c1_node c1_sign r3_node r3_sign : Int) : Prop := ((¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))))
theorem normalization_6343 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1770 c1_node c1_sign r3_node r3_sign) ↔ (shared_expr_Repair066_58 c1_node c1_sign r3_node r3_sign) := (or_congr (normalization_6197 c1_node r3_node) (or_congr (normalization_1841 c1_sign) (or_congr (normalization_1843 c1_sign) (normalization_4702 r3_sign))))

theorem normalization_6344 (c1_node c1_sign r3_node r3_sign : Int) : (¬ (formula_1770 c1_node c1_sign r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_58 c1_node c1_sign r3_node r3_sign)) := (not_congr (normalization_6343 c1_node c1_sign r3_node r3_sign))

theorem normalization_6345 (c1_node c1_sign r3_node r3_sign : Int) : ((¬ (formula_1769 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1770 c1_node c1_sign r3_node r3_sign))) ↔ ((¬ (shared_expr_Repair066_57 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Repair066_58 c1_node c1_sign r3_node r3_sign))) := (or_congr (normalization_6342 c1_node c1_sign r3_node r3_sign) (normalization_6344 c1_node c1_sign r3_node r3_sign))

theorem normalization_6346 (c1_node c1_sign r3_node r3_sign : Int) : (¬ ((¬ (formula_1769 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1770 c1_node c1_sign r3_node r3_sign)))) ↔ (¬ ((¬ (shared_expr_Repair066_57 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Repair066_58 c1_node c1_sign r3_node r3_sign)))) := (not_congr (normalization_6345 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Repair066_59 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∨ (¬ ((¬ (shared_expr_Repair066_57 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Repair066_58 c1_node c1_sign r3_node r3_sign)))))
theorem normalization_6347 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : (formula_1771 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (shared_expr_Repair066_59 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) := (or_congr (normalization_6337 c1_depth r3_depth) (or_congr (normalization_6339 c1_depth r3_depth) (normalization_6346 c1_node c1_sign r3_node r3_sign)))

theorem normalization_6348 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : (¬ (formula_1771 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_59 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)) := (not_congr (normalization_6347 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))

abbrev shared_expr_Repair066_60 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair066_56 c1_node c1_sign h r3_depth r3_node r3_sign)))) ∨ (¬ (shared_expr_Repair066_59 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)))
theorem normalization_6349 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1772 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Repair066_60 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_6335 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_6348 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))

abbrev shared_expr_Repair066_61 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))) ∧ (shared_expr_Repair066_60 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair066_62 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∧ (shared_expr_Repair066_53 c1_depth c1_kind h r3_kind)) ∨ (shared_expr_Repair066_61 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_6350 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1773 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_62 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_6319 c1_kind r3_kind) (normalization_6320 c1_depth c1_kind h r3_kind)) (and_congr (not_congr (normalization_6319 c1_kind r3_kind)) (normalization_6349 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)))

abbrev shared_expr_Repair066_63 (c1_depth c1_kind h r3_kind : Int) : Prop := ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair066_64 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ∧ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair066_65 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair066_66 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Repair066_64 c1_node c1_sign h r3_depth r3_node r3_sign) ∨ (shared_expr_Repair066_65 c1_node c1_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair066_67 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
abbrev shared_expr_Repair066_68 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair066_69 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Repair066_67 c1_node c1_sign r3_node r3_sign) ∨ (shared_expr_Repair066_68 c1_node c1_sign r3_node r3_sign)))
abbrev shared_expr_Repair066_70 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair066_66 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (shared_expr_Repair066_69 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))
abbrev shared_expr_Repair066_71 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Repair066_70 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair066_72 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (¬ (shared_expr_Repair066_63 c1_depth c1_kind h r3_kind))) ∨ (shared_expr_Repair066_71 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_6351 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1856 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1773 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) ↔ ((shared_expr_Repair066_72 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_62 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) := (iff_congr (normalization_6203 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (normalization_6350 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_3857 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1856 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1773 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) := by
  classical
  have ht := (normalized_1589 ((r3_kind) ≤ (2 : Int)) ((r3_kind) ≤ (1 : Int)) ((c1_kind) ≤ (2 : Int)) ((c1_kind) ≤ (1 : Int)) ((c1_kind) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)) ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)) ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)) ((c1_sign) ≤ (2 : Int)) ((c1_sign) ≤ (1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6351 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

abbrev shared_expr_Repair066_73 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∧ (formula_1761 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ∧ (formula_1773 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1869 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair066_73 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair066_74 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((formula_1857 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1869 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
abbrev formula_1870 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair066_74 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

theorem normalized_1590 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6352 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_6353 (c1_level r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := (not_congr (normalization_6352 c1_level r3_depth))

theorem normalization_6354 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) ≥ (-1 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_6355 (c1_level r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≥ (-1 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) := (not_congr (normalization_6354 c1_level r3_depth))

abbrev shared_expr_Repair066_75 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))))
theorem normalization_6356 (c1_level r3_depth r3_kind r3_sign : Int) : (formula_1750 c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair066_75 c1_level r3_depth r3_kind r3_sign) := (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_4697 r3_sign) (or_congr (normalization_6353 c1_level r3_depth) (normalization_6355 c1_level r3_depth)))))

theorem normalization_6357 (c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1750 c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Repair066_75 c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_6356 c1_level r3_depth r3_kind r3_sign))

theorem normalization_6358 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6359 (c1_level r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_6358 c1_level r3_depth))

theorem normalization_6360 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6361 (c1_level r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (not_congr (normalization_6360 c1_level r3_depth))

abbrev shared_expr_Repair066_76 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_6362 (c1_level r3_depth r3_kind r3_sign : Int) : (formula_1751 c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair066_76 c1_level r3_depth r3_kind r3_sign) := (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_4697 r3_sign) (or_congr (normalization_6359 c1_level r3_depth) (normalization_6361 c1_level r3_depth)))))

theorem normalization_6363 (c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1751 c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Repair066_76 c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_6362 c1_level r3_depth r3_kind r3_sign))

abbrev shared_expr_Repair066_77 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair066_75 c1_level r3_depth r3_kind r3_sign))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_76 c1_level r3_depth r3_kind r3_sign))))
theorem normalization_6364 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (formula_1752 c1_group c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair066_77 c1_group c1_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_6357 c1_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_6363 c1_level r3_depth r3_kind r3_sign)))

theorem normalization_6365 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1752 c1_group c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Repair066_77 c1_group c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_6364 c1_group c1_level r3_depth r3_kind r3_sign))

theorem normalization_6366 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : ((¬ (c1_mode ≤ (0 : Int))) ∨ (¬ (c1_mode ≥ (0 : Int))) ∨ (¬ (formula_1752 c1_group c1_level r3_depth r3_kind r3_sign))) ↔ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair066_77 c1_group c1_level r3_depth r3_kind r3_sign))) := (or_congr (normalization_2094 c1_mode) (or_congr (normalization_2096 c1_mode) (normalization_6365 c1_group c1_level r3_depth r3_kind r3_sign)))

theorem normalization_6367 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (0 : Int))) ∨ (¬ (c1_mode ≥ (0 : Int))) ∨ (¬ (formula_1752 c1_group c1_level r3_depth r3_kind r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair066_77 c1_group c1_level r3_depth r3_kind r3_sign)))) := (not_congr (normalization_6366 c1_group c1_level c1_mode r3_depth r3_kind r3_sign))

abbrev shared_expr_Repair066_78 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_6368 (c1_level r3_depth r3_kind r3_sign : Int) : (formula_1748 c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair066_78 c1_level r3_depth r3_kind r3_sign) := (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_4702 r3_sign) (or_congr (normalization_6359 c1_level r3_depth) (normalization_6361 c1_level r3_depth)))))

theorem normalization_6369 (c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1748 c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Repair066_78 c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_6368 c1_level r3_depth r3_kind r3_sign))

abbrev shared_expr_Repair066_79 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))))
theorem normalization_6370 (c1_level r3_depth r3_kind r3_sign : Int) : (formula_1747 c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair066_79 c1_level r3_depth r3_kind r3_sign) := (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_4702 r3_sign) (or_congr (normalization_6353 c1_level r3_depth) (normalization_6355 c1_level r3_depth)))))

theorem normalization_6371 (c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1747 c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Repair066_79 c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_6370 c1_level r3_depth r3_kind r3_sign))

abbrev shared_expr_Repair066_80 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair066_78 c1_level r3_depth r3_kind r3_sign))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_79 c1_level r3_depth r3_kind r3_sign))))
theorem normalization_6372 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (formula_1749 c1_group c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair066_80 c1_group c1_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_6369 c1_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_6371 c1_level r3_depth r3_kind r3_sign)))

theorem normalization_6373 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1749 c1_group c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Repair066_80 c1_group c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_6372 c1_group c1_level r3_depth r3_kind r3_sign))

theorem normalization_6374 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : ((¬ (c1_mode ≤ (1 : Int))) ∨ (¬ (c1_mode ≥ (1 : Int))) ∨ (¬ (formula_1749 c1_group c1_level r3_depth r3_kind r3_sign))) ↔ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair066_80 c1_group c1_level r3_depth r3_kind r3_sign))) := (or_congr (normalization_2123 c1_mode) (or_congr (normalization_2125 c1_mode) (normalization_6373 c1_group c1_level r3_depth r3_kind r3_sign)))

theorem normalization_6375 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (1 : Int))) ∨ (¬ (c1_mode ≥ (1 : Int))) ∨ (¬ (formula_1749 c1_group c1_level r3_depth r3_kind r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair066_80 c1_group c1_level r3_depth r3_kind r3_sign)))) := (not_congr (normalization_6374 c1_group c1_level c1_mode r3_depth r3_kind r3_sign))

abbrev shared_expr_Repair066_81 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_6376 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1753 c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_81 c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_4697 r3_sign) (or_congr (normalization_4737 r3_node) (or_congr (normalization_6359 c1_level r3_depth) (normalization_6361 c1_level r3_depth))))))

theorem normalization_6377 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1753 c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_81 c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_6376 c1_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_82 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_81 c1_level r3_depth r3_kind r3_node r3_sign))))
theorem normalization_6378 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1754 c1_group c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_82 c1_group c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_1386 r3_kind)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_6377 c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_6379 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1754 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_82 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_6378 c1_group c1_level r3_depth r3_kind r3_node r3_sign))

theorem normalization_6380 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (c1_mode ≤ (2 : Int))) ∨ (¬ (c1_mode ≥ (2 : Int))) ∨ (¬ (formula_1754 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) ↔ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair066_82 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) := (or_congr (normalization_2135 c1_mode) (or_congr (normalization_2137 c1_mode) (normalization_6379 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_6381 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (2 : Int))) ∨ (¬ (c1_mode ≥ (2 : Int))) ∨ (¬ (formula_1754 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair066_82 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) := (not_congr (normalization_6380 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_83 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_6382 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1755 c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_83 c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_4697 r3_sign) (or_congr (normalization_4745 r3_node) (or_congr (normalization_6359 c1_level r3_depth) (normalization_6361 c1_level r3_depth))))))

theorem normalization_6383 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1755 c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_83 c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_6382 c1_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_84 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_83 c1_level r3_depth r3_kind r3_node r3_sign))))
theorem normalization_6384 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1756 c1_group c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_84 c1_group c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_1386 r3_kind)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_6383 c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_6385 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1756 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_84 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_6384 c1_group c1_level r3_depth r3_kind r3_node r3_sign))

theorem normalization_6386 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (c1_mode ≤ (3 : Int))) ∨ (¬ (c1_mode ≥ (3 : Int))) ∨ (¬ (formula_1756 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) ↔ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair066_84 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) := (or_congr (normalization_2147 c1_mode) (or_congr (normalization_2149 c1_mode) (normalization_6385 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_6387 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (3 : Int))) ∨ (¬ (c1_mode ≥ (3 : Int))) ∨ (¬ (formula_1756 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair066_84 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) := (not_congr (normalization_6386 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_85 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_6388 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1757 c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_85 c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_4702 r3_sign) (or_congr (normalization_4737 r3_node) (or_congr (normalization_6359 c1_level r3_depth) (normalization_6361 c1_level r3_depth))))))

theorem normalization_6389 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1757 c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_85 c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_6388 c1_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_86 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_85 c1_level r3_depth r3_kind r3_node r3_sign))))
theorem normalization_6390 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1758 c1_group c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_86 c1_group c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_1386 r3_kind)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_6389 c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_6391 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1758 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_86 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_6390 c1_group c1_level r3_depth r3_kind r3_node r3_sign))

theorem normalization_6392 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (c1_mode ≤ (4 : Int))) ∨ (¬ (c1_mode ≥ (4 : Int))) ∨ (¬ (formula_1758 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) ↔ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair066_86 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) := (or_congr (normalization_2159 c1_mode) (or_congr (normalization_2161 c1_mode) (normalization_6391 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_6393 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (4 : Int))) ∨ (¬ (c1_mode ≥ (4 : Int))) ∨ (¬ (formula_1758 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair066_86 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) := (not_congr (normalization_6392 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_87 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_6394 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1759 c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_87 c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_2727 r3_kind) (or_congr (normalization_2729 r3_kind) (or_congr (normalization_4702 r3_sign) (or_congr (normalization_4745 r3_node) (or_congr (normalization_6359 c1_level r3_depth) (normalization_6361 c1_level r3_depth))))))

theorem normalization_6395 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1759 c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_87 c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_6394 c1_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_88 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair066_87 c1_level r3_depth r3_kind r3_node r3_sign))))
theorem normalization_6396 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1760 c1_group c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_88 c1_group c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_1386 r3_kind)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_6395 c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_6397 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1760 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Repair066_88 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_6396 c1_group c1_level r3_depth r3_kind r3_node r3_sign))

theorem normalization_6398 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (c1_mode ≤ (5 : Int))) ∨ (¬ (c1_mode ≥ (5 : Int))) ∨ (¬ (formula_1760 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) ↔ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair066_88 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) := (or_congr (normalization_2169 c1_mode) (or_congr (normalization_2171 c1_mode) (normalization_6397 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_6399 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (5 : Int))) ∨ (¬ (c1_mode ≥ (5 : Int))) ∨ (¬ (formula_1760 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair066_88 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) := (not_congr (normalization_6398 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_89 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair066_77 c1_group c1_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair066_80 c1_group c1_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair066_82 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair066_84 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair066_86 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair066_88 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))))
theorem normalization_6400 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (formula_1761 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_89 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_6367 c1_group c1_level c1_mode r3_depth r3_kind r3_sign) (or_congr (normalization_6375 c1_group c1_level c1_mode r3_depth r3_kind r3_sign) (or_congr (normalization_6381 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_6387 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_6393 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (normalization_6399 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))))))

abbrev shared_expr_Repair066_90 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_91 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_92 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_90 c1_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair066_91 c1_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Repair066_93 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_94 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_95 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_93 c1_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair066_94 c1_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Repair066_96 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair066_97 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_96 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_98 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair066_99 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_98 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_100 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair066_101 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_100 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_102 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair066_103 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_102 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair066_104 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_mode) ≤ (0 : Int)) ∧ (¬ ((c1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair066_92 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((((c1_mode) ≤ (1 : Int)) ∧ (¬ ((c1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair066_95 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((((c1_mode) ≤ (2 : Int)) ∧ (¬ ((c1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair066_97 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (3 : Int)) ∧ (¬ ((c1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair066_99 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (4 : Int)) ∧ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair066_101 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (5 : Int)) ∧ (¬ ((c1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair066_103 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))
theorem normalization_6401 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1853 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (formula_1761 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ↔ ((shared_expr_Repair066_104 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_89 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) := (iff_congr (normalization_6185 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (normalization_6400 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Repair066_105 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair066_89 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair066_62 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
theorem normalization_6402 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1869 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_105 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_1683 c1_kind) (normalization_6400 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) (and_congr (not_congr (normalization_1683 c1_kind)) (normalization_6350 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Repair066_106 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair066_104 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair066_72 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Repair066_107 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Repair066_106 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_105 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_6403 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1870 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_107 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (iff_congr (normalization_6204 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (normalization_6402 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_3858 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1870 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
  classical
  have ht := (normalized_1590 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Repair066_104 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (shared_expr_Repair066_89 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (shared_expr_Repair066_72 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Repair066_62 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1685 c1_kind) (replay_319 c1_kind)
  have n1 : ((shared_expr_Repair066_104 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_89 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) := by
    exact Iff.mp (normalization_6401 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (replay_3856 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)
  have n2 : ((shared_expr_Repair066_72 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair066_62 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) := by
    exact Iff.mp (normalization_6351 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (replay_3857 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6403 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

end H4Formal.Generated.Repair
