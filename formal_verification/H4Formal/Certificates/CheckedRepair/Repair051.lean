import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair050

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_1185 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_0 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))))
theorem normalization_5047 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Repair051_0 c1_depth c2_depth) := (iff_congr (normalization_4939 c1_depth c2_depth) (normalization_5045 c1_depth c2_depth))

-- Checked replay of trans.
abbrev shared_expr_Repair051_1 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))
theorem replay_2861 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1185 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) (shared_expr_Repair051_0 c1_depth c2_depth))
  have n0 : (shared_expr_Repair051_1 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5041 c1_depth c2_depth) (replay_2859 c1_depth c2_depth)
  have n1 : (shared_expr_Repair051_0 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5046 c1_depth c2_depth) (replay_2860 c1_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5047 c1_depth c2_depth) hn

theorem normalized_1186 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5048 (c1_depth c2_depth : Int) : (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))) := (not_congr (normalization_5045 c1_depth c2_depth))

abbrev shared_expr_Repair051_2 (c1_depth c2_depth : Int) : Prop := ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ↔ (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))))
theorem normalization_5049 (c1_depth c2_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))) ↔ (shared_expr_Repair051_2 c1_depth c2_depth) := (iff_congr (normalization_4940 c1_depth c2_depth) (normalization_5048 c1_depth c2_depth))

-- Checked replay of monotonicity.
theorem replay_2862 (c1_depth c2_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_1186 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair051_0 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5047 c1_depth c2_depth) (replay_2861 c1_depth c2_depth)
  have hn := ht n0
  exact Iff.mpr (normalization_5049 c1_depth c2_depth) hn

abbrev shared_expr_Repair051_3 (c1_depth c2_depth : Int) : Prop := ((¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))
abbrev formula_1420 (c1_depth c2_depth : Int) : Prop := (shared_expr_Repair051_3 c1_depth c2_depth)

theorem normalized_1187 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_4 (c1_depth c2_depth : Int) : Prop := ((¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
theorem normalization_5050 (c1_depth c2_depth : Int) : (formula_1420 c1_depth c2_depth) ↔ (shared_expr_Repair051_4 c1_depth c2_depth) := (iff_congr (normalization_5048 c1_depth c2_depth) (normalization_5044 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2863 (c1_depth c2_depth : Int) : (formula_1420 c1_depth c2_depth) := by
  classical
  have ht := (normalized_1187 ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_5050 c1_depth c2_depth) hn

theorem normalized_1188 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_5 (c1_depth c2_depth : Int) : Prop := ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
theorem normalization_5051 (c1_depth c2_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (shared_expr_Repair051_5 c1_depth c2_depth) := (iff_congr (normalization_4940 c1_depth c2_depth) (normalization_5044 c1_depth c2_depth))

-- Checked replay of trans.
theorem replay_2864 (c1_depth c2_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) := by
  classical
  have ht := (normalized_1188 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair051_2 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5049 c1_depth c2_depth) (replay_2862 c1_depth c2_depth)
  have n1 : (shared_expr_Repair051_4 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5050 c1_depth c2_depth) (replay_2863 c1_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5051 c1_depth c2_depth) hn

theorem normalized_1189 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5052 (c1_node c2_node : Int) : ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5053 (c1_node c2_node : Int) : (((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (and_congr (normalization_4942 c1_node c2_node) (normalization_5052 c1_node c2_node))

abbrev shared_expr_Repair051_6 (c1_node c2_node : Int) : Prop := (((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_5054 (c1_node c2_node : Int) : (((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Repair051_6 c1_node c2_node) := (iff_congr (normalization_4941 c1_node c2_node) (normalization_5053 c1_node c2_node))

-- Checked replay of rewrite.
theorem replay_2865 (c1_node c2_node : Int) : (((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1189 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5054 c1_node c2_node) hn

abbrev shared_expr_Repair051_7 (c1_node c2_node : Int) : Prop := ((((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1421 (c1_node c2_node : Int) : Prop := (shared_expr_Repair051_7 c1_node c2_node)

theorem normalized_1190 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5055 (c1_node c2_node : Int) : (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_5052 c1_node c2_node))

theorem normalization_5056 (c1_node c2_node : Int) : ((¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) := (or_congr (normalization_4943 c1_node c2_node) (normalization_5055 c1_node c2_node))

theorem normalization_5057 (c1_node c2_node : Int) : (¬ ((¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) := (not_congr (normalization_5056 c1_node c2_node))

abbrev shared_expr_Repair051_8 (c1_node c2_node : Int) : Prop := (((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
theorem normalization_5058 (c1_node c2_node : Int) : (formula_1421 c1_node c2_node) ↔ (shared_expr_Repair051_8 c1_node c2_node) := (iff_congr (normalization_5053 c1_node c2_node) (normalization_5057 c1_node c2_node))

-- Checked replay of rewrite.
theorem replay_2866 (c1_node c2_node : Int) : (formula_1421 c1_node c2_node) := by
  classical
  have ht := (normalized_1190 (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5058 c1_node c2_node) hn

abbrev shared_expr_Repair051_9 (c1_node c2_node : Int) : Prop := (((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1422 (c1_node c2_node : Int) : Prop := (shared_expr_Repair051_9 c1_node c2_node)

theorem normalized_1191 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5059 (c1_node c2_node : Int) : (formula_1422 c1_node c2_node) ↔ (shared_expr_Repair051_8 c1_node c2_node) := (iff_congr (normalization_4941 c1_node c2_node) (normalization_5057 c1_node c2_node))

-- Checked replay of trans.
theorem replay_2867 (c1_node c2_node : Int) : (formula_1422 c1_node c2_node) := by
  classical
  have ht := (normalized_1191 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) (shared_expr_Repair051_8 c1_node c2_node))
  have n0 : (shared_expr_Repair051_6 c1_node c2_node) := by
    exact Iff.mp (normalization_5054 c1_node c2_node) (replay_2865 c1_node c2_node)
  have n1 : (shared_expr_Repair051_8 c1_node c2_node) := by
    exact Iff.mp (normalization_5058 c1_node c2_node) (replay_2866 c1_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5059 c1_node c2_node) hn

abbrev shared_expr_Repair051_10 (c1_node c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair051_11 (c1_node c2_node : Int) : Prop := ((¬ (¬ ((¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_1423 (c1_node c2_node c2_sign : Int) : Prop := ((shared_expr_Repair051_10 c1_node c2_node c2_sign) ∨ (shared_expr_Repair051_11 c1_node c2_node))

theorem normalized_1192 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_12 (c1_node c2_node c2_sign : Int) : Prop := ((¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair051_13 (c1_node c2_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))))) ∧ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_5060 (c1_node c2_node c2_sign : Int) : (formula_1423 c1_node c2_node c2_sign) ↔ ((shared_expr_Repair051_12 c1_node c2_node c2_sign) ∨ (shared_expr_Repair051_13 c1_node c2_node)) := (or_congr (and_congr (normalization_5057 c1_node c2_node) (normalization_119 c2_sign)) (and_congr (not_congr (normalization_5057 c1_node c2_node)) (normalization_4943 c1_node c2_node)))

abbrev shared_expr_Repair051_14 (c1_node c2_node : Int) : Prop := ((¬ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair051_15 (c1_node c2_node c2_sign : Int) : Prop := ((((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_14 c1_node c2_node))
theorem normalization_5061 (c1_node c2_node c2_sign : Int) : ((formula_1401 c1_node c2_node c2_sign) ↔ (formula_1423 c1_node c2_node c2_sign)) ↔ ((shared_expr_Repair051_15 c1_node c2_node c2_sign) ↔ ((shared_expr_Repair051_12 c1_node c2_node c2_sign) ∨ (shared_expr_Repair051_13 c1_node c2_node))) := (iff_congr (normalization_4944 c1_node c2_node c2_sign) (normalization_5060 c1_node c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2868 (c1_node c2_node c2_sign : Int) : ((formula_1401 c1_node c2_node c2_sign) ↔ (formula_1423 c1_node c2_node c2_sign)) := by
  classical
  have ht := (normalized_1192 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair051_8 c1_node c2_node) := by
    exact Iff.mp (normalization_5059 c1_node c2_node) (replay_2867 c1_node c2_node)
  have n1 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3121 c2_sign) (replay_2180 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5061 c1_node c2_node c2_sign) hn

theorem normalized_1193 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_16 (c1_node c2_node : Int) : Prop := (((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_5062 (c1_node c2_node c2_sign : Int) : (formula_1376 c1_node c2_node c2_sign) ↔ ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign)) := (or_congr (and_congr (normalization_5056 c1_node c2_node) (normalization_4943 c1_node c2_node)) (and_congr (not_congr (normalization_5056 c1_node c2_node)) (normalization_119 c2_sign)))

theorem normalization_5063 (c1_node c2_node c2_sign : Int) : ((formula_1423 c1_node c2_node c2_sign) ↔ (formula_1376 c1_node c2_node c2_sign)) ↔ (((shared_expr_Repair051_12 c1_node c2_node c2_sign) ∨ (shared_expr_Repair051_13 c1_node c2_node)) ↔ ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign))) := (iff_congr (normalization_5060 c1_node c2_node c2_sign) (normalization_5062 c1_node c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2869 (c1_node c2_node c2_sign : Int) : ((formula_1423 c1_node c2_node c2_sign) ↔ (formula_1376 c1_node c2_node c2_sign)) := by
  classical
  have ht := (normalized_1193 ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5063 c1_node c2_node c2_sign) hn

theorem normalized_1194 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5064 (c1_node c2_node c2_sign : Int) : ((formula_1401 c1_node c2_node c2_sign) ↔ (formula_1376 c1_node c2_node c2_sign)) ↔ ((shared_expr_Repair051_15 c1_node c2_node c2_sign) ↔ ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign))) := (iff_congr (normalization_4944 c1_node c2_node c2_sign) (normalization_5062 c1_node c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2870 (c1_node c2_node c2_sign : Int) : ((formula_1401 c1_node c2_node c2_sign) ↔ (formula_1376 c1_node c2_node c2_sign)) := by
  classical
  have ht := (normalized_1194 (shared_expr_Repair051_15 c1_node c2_node c2_sign) ((shared_expr_Repair051_12 c1_node c2_node c2_sign) ∨ (shared_expr_Repair051_13 c1_node c2_node)) ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign)))
  have n0 : ((shared_expr_Repair051_15 c1_node c2_node c2_sign) ↔ ((shared_expr_Repair051_12 c1_node c2_node c2_sign) ∨ (shared_expr_Repair051_13 c1_node c2_node))) := by
    exact Iff.mp (normalization_5061 c1_node c2_node c2_sign) (replay_2868 c1_node c2_node c2_sign)
  have n1 : (((shared_expr_Repair051_12 c1_node c2_node c2_sign) ∨ (shared_expr_Repair051_13 c1_node c2_node)) ↔ ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign))) := by
    exact Iff.mp (normalization_5063 c1_node c2_node c2_sign) (replay_2869 c1_node c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5064 c1_node c2_node c2_sign) hn

abbrev shared_expr_Repair051_17 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ∨ (formula_1401 c1_node c2_node c2_sign)) ↔ (((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ∨ (formula_1376 c1_node c2_node c2_sign)))
abbrev formula_1424 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_17 c1_depth c1_node c2_depth c2_node c2_sign)

theorem normalized_1195 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_18 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign)))
theorem normalization_5065 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : (((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ∨ (formula_1376 c1_node c2_node c2_sign)) ↔ (shared_expr_Repair051_18 c1_depth c1_node c2_depth c2_node c2_sign) := (or_congr (normalization_5044 c1_depth c2_depth) (normalization_5062 c1_node c2_node c2_sign))

abbrev shared_expr_Repair051_19 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_15 c1_node c2_node c2_sign)) ↔ (shared_expr_Repair051_18 c1_depth c1_node c2_depth c2_node c2_sign))
theorem normalization_5066 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : (formula_1424 c1_depth c1_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_19 c1_depth c1_node c2_depth c2_node c2_sign) := (iff_congr (normalization_4945 c1_depth c1_node c2_depth c2_node c2_sign) (normalization_5065 c1_depth c1_node c2_depth c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2871 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : (formula_1424 c1_depth c1_node c2_depth c2_node c2_sign) := by
  classical
  have ht := (normalized_1195 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) (shared_expr_Repair051_15 c1_node c2_node c2_sign) ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign)))
  have n0 : (shared_expr_Repair051_5 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5051 c1_depth c2_depth) (replay_2864 c1_depth c2_depth)
  have n1 : ((shared_expr_Repair051_15 c1_node c2_node c2_sign) ↔ ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign))) := by
    exact Iff.mp (normalization_5064 c1_node c2_node c2_sign) (replay_2870 c1_node c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5066 c1_depth c1_node c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair051_20 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := ((((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ∨ (formula_1376 c1_node c2_node c2_sign)) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_1376 c1_node c2_node c2_sign)))
abbrev formula_1425 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_20 c1_depth c1_node c2_depth c2_node c2_sign)

theorem normalized_1196 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_21 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ∨ ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign)))
theorem normalization_5067 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_1376 c1_node c2_node c2_sign)) ↔ (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign) := (or_congr (normalization_5042 c1_depth c2_depth) (or_congr (normalization_5043 c1_depth c2_depth) (normalization_5062 c1_node c2_node c2_sign)))

theorem normalization_5068 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : (formula_1425 c1_depth c1_node c2_depth c2_node c2_sign) ↔ ((shared_expr_Repair051_18 c1_depth c1_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign)) := (iff_congr (normalization_5065 c1_depth c1_node c2_depth c2_node c2_sign) (normalization_5067 c1_depth c1_node c2_depth c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2872 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : (formula_1425 c1_depth c1_node c2_depth c2_node c2_sign) := by
  classical
  have ht := (normalized_1196 ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((shared_expr_Repair051_16 c1_node c2_node) ∨ (shared_expr_Repair051_12 c1_node c2_node c2_sign)))
  have hn := ht
  exact Iff.mpr (normalization_5068 c1_depth c1_node c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair051_22 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ∨ (formula_1401 c1_node c2_node c2_sign)) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_1376 c1_node c2_node c2_sign)))
abbrev formula_1426 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_22 c1_depth c1_node c2_depth c2_node c2_sign)

theorem normalized_1197 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_23 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_15 c1_node c2_node c2_sign)) ↔ (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign))
theorem normalization_5069 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : (formula_1426 c1_depth c1_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_23 c1_depth c1_node c2_depth c2_node c2_sign) := (iff_congr (normalization_4945 c1_depth c1_node c2_depth c2_node c2_sign) (normalization_5067 c1_depth c1_node c2_depth c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2873 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : (formula_1426 c1_depth c1_node c2_depth c2_node c2_sign) := by
  classical
  have ht := (normalized_1197 ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_15 c1_node c2_node c2_sign)) (shared_expr_Repair051_18 c1_depth c1_node c2_depth c2_node c2_sign) (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign))
  have n0 : (shared_expr_Repair051_19 c1_depth c1_node c2_depth c2_node c2_sign) := by
    exact Iff.mp (normalization_5066 c1_depth c1_node c2_depth c2_node c2_sign) (replay_2871 c1_depth c1_node c2_depth c2_node c2_sign)
  have n1 : ((shared_expr_Repair051_18 c1_depth c1_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_5068 c1_depth c1_node c2_depth c2_node c2_sign) (replay_2872 c1_depth c1_node c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5069 c1_depth c1_node c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair051_24 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))))) ∧ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_1376 c1_node c2_node c2_sign)))
abbrev shared_expr_Repair051_25 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))) ∧ (formula_1377 c1_node c1_sign c2_node)) ∨ (shared_expr_Repair051_24 c1_depth c1_node c2_depth c2_node c2_sign))
abbrev formula_1427 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_25 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)

theorem normalized_1198 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_26 (c1_node c2_node : Int) : Prop := (((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair051_27 (c1_node c1_sign c2_node : Int) : Prop := ((¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Repair051_28 (c1_depth c1_node c1_sign c2_depth c2_node : Int) : Prop := ((¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))) ∧ ((shared_expr_Repair051_26 c1_node c2_node) ∨ (shared_expr_Repair051_27 c1_node c1_sign c2_node)))
abbrev shared_expr_Repair051_29 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))))) ∧ (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign))
theorem normalization_5070 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : (formula_1427 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ ((shared_expr_Repair051_28 c1_depth c1_node c1_sign c2_depth c2_node) ∨ (shared_expr_Repair051_29 c1_depth c1_node c2_depth c2_node c2_sign)) := (or_congr (and_congr (normalization_5022 c1_depth c2_depth) (normalization_5035 c1_node c1_sign c2_node)) (and_congr (not_congr (normalization_5022 c1_depth c2_depth)) (normalization_5067 c1_depth c1_node c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair051_30 (c1_node c2_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair051_31 (c1_node c1_sign c2_node : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair051_30 c1_node c2_node))
abbrev shared_expr_Repair051_32 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_15 c1_node c2_node c2_sign)))
abbrev shared_expr_Repair051_33 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair051_31 c1_node c1_sign c2_node)) ∨ (shared_expr_Repair051_32 c1_depth c1_node c2_depth c2_node c2_sign))
abbrev shared_expr_Repair051_34 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := ((shared_expr_Repair051_33 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ ((shared_expr_Repair051_28 c1_depth c1_node c1_sign c2_depth c2_node) ∨ (shared_expr_Repair051_29 c1_depth c1_node c2_depth c2_node c2_sign)))
theorem normalization_5071 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1402 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1427 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (shared_expr_Repair051_34 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := (iff_congr (normalization_4946 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (normalization_5070 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair051_35 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))))
theorem replay_2874 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1402 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1427 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_1198 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) (shared_expr_Repair051_31 c1_node c1_sign c2_node) ((shared_expr_Repair051_26 c1_node c2_node) ∨ (shared_expr_Repair051_27 c1_node c1_sign c2_node)) ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_15 c1_node c2_node c2_sign)) (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign))
  have n0 : (shared_expr_Repair051_35 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5024 c1_depth c2_depth) (replay_2852 c1_depth c2_depth)
  have n1 : ((shared_expr_Repair051_31 c1_node c1_sign c2_node) ↔ ((shared_expr_Repair051_26 c1_node c2_node) ∨ (shared_expr_Repair051_27 c1_node c1_sign c2_node))) := by
    exact Iff.mp (normalization_5037 c1_node c1_sign c2_node) (replay_2858 c1_node c1_sign c2_node)
  have n2 : (shared_expr_Repair051_23 c1_depth c1_node c2_depth c2_node c2_sign) := by
    exact Iff.mp (normalization_5069 c1_depth c1_node c2_depth c2_node c2_sign) (replay_2873 c1_depth c1_node c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5071 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) hn

theorem normalized_1199 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_36 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := ((((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign)) ∨ (shared_expr_Repair051_28 c1_depth c1_node c1_sign c2_depth c2_node))
theorem normalization_5072 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : (formula_1378 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_5021 c1_depth c2_depth) (normalization_5067 c1_depth c1_node c2_depth c2_node c2_sign)) (and_congr (not_congr (normalization_5021 c1_depth c2_depth)) (normalization_5035 c1_node c1_sign c2_node)))

abbrev shared_expr_Repair051_37 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((shared_expr_Repair051_28 c1_depth c1_node c1_sign c2_depth c2_node) ∨ (shared_expr_Repair051_29 c1_depth c1_node c2_depth c2_node c2_sign)) ↔ (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
theorem normalization_5073 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1427 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1378 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (shared_expr_Repair051_37 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := (iff_congr (normalization_5070 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (normalization_5072 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2875 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1427 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1378 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_1199 ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ((shared_expr_Repair051_26 c1_node c2_node) ∨ (shared_expr_Repair051_27 c1_node c1_sign c2_node)) (shared_expr_Repair051_21 c1_depth c1_node c2_depth c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_5073 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) hn

theorem normalized_1200 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5074 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1402 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1378 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ ((shared_expr_Repair051_33 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := (iff_congr (normalization_4946 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (normalization_5072 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2876 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1402 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1378 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_1200 (shared_expr_Repair051_33 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ((shared_expr_Repair051_28 c1_depth c1_node c1_sign c2_depth c2_node) ∨ (shared_expr_Repair051_29 c1_depth c1_node c2_depth c2_node c2_sign)) (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
  have n0 : (shared_expr_Repair051_34 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := by
    exact Iff.mp (normalization_5071 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (replay_2874 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)
  have n1 : (shared_expr_Repair051_37 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := by
    exact Iff.mp (normalization_5073 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (replay_2875 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5074 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair051_38 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_1379 c1_node c1_sign c2_node c2_sign)) ∨ ((¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ∧ (formula_1378 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
abbrev formula_1428 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_38 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)

theorem normalized_1201 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_39 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair051_40 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair051_39 c1_node c1_sign c2_node c2_sign))
abbrev shared_expr_Repair051_41 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
abbrev shared_expr_Repair051_42 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair051_40 c1_node c1_sign c2_node c2_sign)) ∨ (shared_expr_Repair051_41 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
theorem normalization_5075 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : (formula_1428 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_42 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_4981 c1_depth c2_depth) (normalization_5012 c1_node c1_sign c2_node c2_sign)) (and_congr (not_congr (normalization_4981 c1_depth c2_depth)) (normalization_5072 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair051_43 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair051_44 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair051_43 c1_node c1_sign c2_node c2_sign) ∨ ((¬ (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair051_45 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair051_44 c1_node c1_sign c2_node c2_sign)) ∨ ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_33 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
theorem normalization_5076 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1428 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ ((shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_42 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := (iff_congr (normalization_4947 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (normalization_5075 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair051_46 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))))
theorem replay_2877 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1428 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_1201 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) (shared_expr_Repair051_44 c1_node c1_sign c2_node c2_sign) (shared_expr_Repair051_40 c1_node c1_sign c2_node c2_sign) (shared_expr_Repair051_33 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
  have n0 : (shared_expr_Repair051_46 c1_depth c2_depth) := by
    exact Iff.mp (normalization_4984 c1_depth c2_depth) (replay_2833 c1_depth c2_depth)
  have n1 : ((shared_expr_Repair051_44 c1_node c1_sign c2_node c2_sign) ↔ (shared_expr_Repair051_40 c1_node c1_sign c2_node c2_sign)) := by
    exact Iff.mp (normalization_5014 c1_node c1_sign c2_node c2_sign) (replay_2849 c1_node c1_sign c2_node c2_sign)
  have n2 : ((shared_expr_Repair051_33 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_5074 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (replay_2876 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5076 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) hn

theorem normalized_1202 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_47 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := ((((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ∨ ((¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair051_40 c1_node c1_sign c2_node c2_sign)))
theorem normalization_5077 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_4980 c1_depth c2_depth) (normalization_5072 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) (and_congr (not_congr (normalization_4980 c1_depth c2_depth)) (normalization_5012 c1_node c1_sign c2_node c2_sign)))

theorem normalization_5078 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1428 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ ((shared_expr_Repair051_42 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := (iff_congr (normalization_5075 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (normalization_5077 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2878 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1428 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_1202 ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) (shared_expr_Repair051_40 c1_node c1_sign c2_node c2_sign) (shared_expr_Repair051_36 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_5078 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) hn

theorem normalized_1203 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5079 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ ((shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := (iff_congr (normalization_4947 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (normalization_5077 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2879 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : ((formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_1203 (shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (shared_expr_Repair051_42 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
  have n0 : ((shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_42 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_5076 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (replay_2877 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)
  have n1 : ((shared_expr_Repair051_42 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_5078 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (replay_2878 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5079 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair051_48 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (c2_kind = (2 : Int))) ∧ (formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ∧ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
abbrev formula_1429 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_48 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_1204 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∧ p2) ↔ (p1 ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5080 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ∧ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := (and_congr (normalization_1075 c2_kind) (normalization_5077 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

abbrev shared_expr_Repair051_49 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
theorem normalization_5081 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1429 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_49 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_4948 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5080 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2880 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1429 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_1204 (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
  have n0 : ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_3081 c2_kind) (replay_2160 c2_kind)
  have n1 : ((shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_5079 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) (replay_2879 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5081 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair051_50 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ∧ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))))
abbrev formula_1430 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_50 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_1205 (p0 p1 : Prop) : ((p0 ∧ p1) ↔ (¬ ((¬ p0) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5082 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : (¬ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := (not_congr (normalization_5077 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

theorem normalization_5083 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))) ↔ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))) := (or_congr (normalization_1076 c2_kind) (normalization_5082 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

theorem normalization_5084 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))) := (not_congr (normalization_5083 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair051_51 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))))
theorem normalization_5085 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1430 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_51 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_5080 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5084 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2881 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1430 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_1205 ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_5085 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair051_52 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (c2_kind = (2 : Int))) ∧ (formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))))
abbrev formula_1431 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_52 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_1206 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_53 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))))
theorem normalization_5086 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1431 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_53 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_4948 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5084 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2882 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1431 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_1206 ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) (((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))))
  have n0 : (shared_expr_Repair051_49 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_5081 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2880 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have n1 : (shared_expr_Repair051_51 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_5085 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2881 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5086 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair051_54 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ∧ (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_1380 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))))
abbrev shared_expr_Repair051_55 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int)))))) ∨ (shared_expr_Repair051_54 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_1432 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_55 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

abbrev shared_expr_Repair051_56 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((c1_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c1_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))) ↔ (formula_1432 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_1433 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_56 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_1207 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_57 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∧ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))))
abbrev shared_expr_Repair051_58 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) ∨ (shared_expr_Repair051_57 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
theorem normalization_5087 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1432 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_58 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_1774 c1_kind) (normalization_3071 c2_kind)) (and_congr (not_congr (normalization_1774 c1_kind)) (normalization_5084 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair051_59 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
abbrev shared_expr_Repair051_60 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_59 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
theorem normalization_5088 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1433 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ ((shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_58 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := (iff_congr (normalization_4949 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5087 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2883 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1433 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_1207 (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_45 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))))
  have n0 : ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1776 c1_kind) (replay_355 c1_kind)
  have n1 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3073 c2_kind) (replay_2154 c2_kind)
  have n2 : (shared_expr_Repair051_53 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_5086 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2882 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5088 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

theorem normalized_1208 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_61 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))))
abbrev shared_expr_Repair051_62 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((shared_expr_Repair051_61 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ∨ ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))))
theorem normalization_5089 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_1773 c1_kind) (normalization_5084 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) (and_congr (not_congr (normalization_1773 c1_kind)) (normalization_3071 c2_kind)))

theorem normalization_5090 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : ((formula_1432 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair051_58 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := (iff_congr (normalization_5087 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5089 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2884 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : ((formula_1432 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := by
  classical
  have ht := (normalized_1208 ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair051_47 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))))
  have hn := ht
  exact Iff.mpr (normalization_5090 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair051_63 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((c1_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c1_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))) ↔ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_1434 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_63 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_1209 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5091 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1434 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ ((shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := (iff_congr (normalization_4949 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5089 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2885 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1434 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_1209 (shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (shared_expr_Repair051_58 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
  have n0 : ((shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_58 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := by
    exact Iff.mp (normalization_5088 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2883 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have n1 : ((shared_expr_Repair051_58 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := by
    exact Iff.mp (normalization_5090 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2884 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5091 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair051_64 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((formula_1404 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∧ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
abbrev formula_1435 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_64 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_1210 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∧ p2) ↔ (p1 ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5092 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∧ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := (and_congr (normalization_1002 c2_kind) (normalization_5089 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair051_65 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_5093 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1435 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_65 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_4950 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5092 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2886 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1435 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_1210 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
  have n0 : ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_3048 c2_kind) (replay_2144 c2_kind)
  have n1 : ((shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := by
    exact Iff.mp (normalization_5091 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2885 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5093 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair051_66 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∧ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev formula_1436 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_66 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_1211 (p0 p1 : Prop) : ((p0 ∧ p1) ↔ (¬ ((¬ p0) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5094 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := (not_congr (normalization_5089 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

theorem normalization_5095 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))) ↔ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))) := (or_congr (normalization_1003 c2_kind) (normalization_5094 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

theorem normalization_5096 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))) := (not_congr (normalization_5095 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair051_67 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))))
theorem normalization_5097 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1436 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_67 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_5092 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5096 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2887 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1436 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_1211 ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_5097 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair051_68 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((formula_1404 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev formula_1437 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_68 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_1212 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_69 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))))
theorem normalization_5098 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1437 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair051_69 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_4950 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (normalization_5096 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2888 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1437 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_1212 ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))))
  have n0 : (shared_expr_Repair051_65 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_5093 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2886 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have n1 : (shared_expr_Repair051_67 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_5097 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2887 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5098 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair051_70 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ∧ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev shared_expr_Repair051_71 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∧ (formula_1382 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) ∨ (shared_expr_Repair051_70 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_1438 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_71 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

abbrev shared_expr_Repair051_72 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_1405 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_1438 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_1439 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_72 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_1213 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_73 (c1_group c1_mode c2_group c2_mode : Int) : Prop := ((((¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c1_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair051_74 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair051_73 c1_group c1_mode c2_group c2_mode)))
abbrev shared_expr_Repair051_75 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair051_74 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c1_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair051_76 (c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair051_75 c1_group c1_level c1_mode c2_group c2_level c2_mode)))
abbrev shared_expr_Repair051_77 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ∧ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))))
theorem normalization_5099 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1438 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ ((shared_expr_Repair051_76 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair051_77 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := (or_congr (and_congr (normalization_1683 c1_kind) (normalization_4965 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) (and_congr (not_congr (normalization_1683 c1_kind)) (normalization_5096 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair051_78 (c1_group c1_mode c2_group c2_mode : Int) : Prop := (((((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c1_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair051_79 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := (((((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair051_78 c1_group c1_mode c2_group c2_mode)) ∨ ((¬ (((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair051_80 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair051_79 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c1_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair051_81 (c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair051_80 c1_group c1_level c1_mode c2_group c2_level c2_mode)))
abbrev shared_expr_Repair051_82 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
abbrev shared_expr_Repair051_83 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair051_81 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair051_82 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair051_76 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair051_77 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_5100 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1439 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair051_83 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_4951 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_5099 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair051_84 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair051_80 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair051_75 c1_group c1_level c1_mode c2_group c2_level c2_mode)))
theorem replay_2889 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1439 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_1213 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair051_80 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair051_75 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_60 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1685 c1_kind) (replay_319 c1_kind)
  have n1 : (shared_expr_Repair051_84 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) := by
    exact Iff.mp (normalization_4967 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) (replay_2826 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)
  have n2 : (shared_expr_Repair051_69 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_5098 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (replay_2888 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5100 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

abbrev shared_expr_Repair051_85 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_1438 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_1383 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_1440 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_85 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_1214 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_86 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))))
theorem normalization_5101 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1383 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ ((shared_expr_Repair051_86 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ∨ (shared_expr_Repair051_76 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode)) := (or_congr (and_congr (normalization_1682 c1_kind) (normalization_5096 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) (and_congr (not_congr (normalization_1682 c1_kind)) (normalization_4965 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)))

abbrev shared_expr_Repair051_87 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair051_76 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair051_77 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair051_86 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ∨ (shared_expr_Repair051_76 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode)))
theorem normalization_5102 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1440 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair051_87 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_5099 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_5101 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2890 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1440 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_1214 ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair051_75 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair051_62 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))))
  have hn := ht
  exact Iff.mpr (normalization_5102 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

abbrev shared_expr_Repair051_88 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_1405 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_1383 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_1441 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_88 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_1215 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair051_89 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair051_81 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair051_82 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair051_86 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ∨ (shared_expr_Repair051_76 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode)))
theorem normalization_5103 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1441 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair051_89 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_4951 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_5101 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2891 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1441 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_1215 ((shared_expr_Repair051_81 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair051_82 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ((shared_expr_Repair051_76 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair051_77 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ((shared_expr_Repair051_86 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ∨ (shared_expr_Repair051_76 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode)))
  have n0 : (shared_expr_Repair051_83 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
    exact Iff.mp (normalization_5100 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2889 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)
  have n1 : (shared_expr_Repair051_87 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
    exact Iff.mp (normalization_5102 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2890 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5103 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

-- Checked replay of mp.
theorem replay_2892 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_1383 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact Iff.mp (replay_2891 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2822 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182)

abbrev shared_expr_Repair051_90 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev formula_1442 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_90 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

-- Checked replay of unit-resolution.
theorem replay_2893 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_1442 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  exact (Or.elim (replay_2816 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (fun l0 => (Or.inl l0)) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_2892 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182)))))))

abbrev shared_expr_Repair051_91 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))) ∨ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))
abbrev formula_1443 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair051_91 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

theorem propositional_1216 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 : Prop) : (((¬ p0) ∨ (¬ ((((¬ p1) ∨ (¬ p2)) ∧ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((((¬ p5) ∨ (¬ p6)) ∧ ((((¬ p7) ∨ (¬ p8)) ∧ ((¬ p9) ∨ (¬ p10) ∨ ((((¬ p11) ∨ (¬ p12)) ∧ (¬ p11)) ∨ ((¬ ((¬ p11) ∨ (¬ p12))) ∧ (¬ ((¬ p13) ∨ (¬ p14))))))) ∨ ((¬ ((¬ p7) ∨ (¬ p8))) ∧ ((((¬ p15) ∨ (¬ p16)) ∧ (¬ p16)) ∨ ((¬ ((¬ p15) ∨ (¬ p16))) ∧ (¬ ((¬ p17) ∨ (¬ p18)))))))) ∨ ((¬ ((¬ p5) ∨ (¬ p6))) ∧ ((((¬ p19) ∨ (¬ p20)) ∧ (¬ p20)) ∨ ((¬ ((¬ p19) ∨ (¬ p20))) ∧ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ p13) ∨ (¬ p14))))))))))) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ (¬ ((¬ p21) ∨ (¬ p22))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2894 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1443 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := by
  exact (propositional_1216 ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) (c1_kind ≤ (2 : Int)) (c1_kind ≥ (2 : Int)) (c2_kind ≤ (2 : Int)) (c2_kind ≥ (2 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)) ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2895 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1381 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))) := by
  exact (Or.elim (replay_2894 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i158 t0))))

-- Checked replay of unit-resolution.
theorem replay_2896 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) := by
  exact (Or.elim (replay_2893 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_2895 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign i158)))))

-- Checked replay of unit-resolution.
theorem replay_2897 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (c1_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_2815 c1_kind) (fun l0 => (False.elim ((replay_2896 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182 i158) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2898 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (¬ (c1_kind ≥ (1 : Int))) := by
  exact (Or.elim (replay_2814 c1_kind) (fun l0 => (False.elim (l0 (replay_2897 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182 i158)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2899 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (¬ (c1_kind ≥ (2 : Int))) := by
  exact (Or.elim (replay_2813 c1_kind) (fun l0 => (False.elim ((replay_2898 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182 i158) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2900 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (formula_1372 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact (Or.elim (replay_2812 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_2899 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182 i158) t0))))

theorem propositional_1217 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p7))))) ∨ (¬ ((((¬ p10) ∨ (¬ p13)) ∧ ((¬ ((¬ p14) ∨ (¬ p15))) ∨ (¬ ((¬ p16) ∨ (¬ p17))))) ∨ ((¬ ((¬ p10) ∨ (¬ p13))) ∧ (¬ ((¬ p18) ∨ (¬ p19))))))) ∨ p9) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2901 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h : Int) : ((formula_1374 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h) ∨ (c1_kind ≥ (1 : Int))) := by
  exact (propositional_1217 (c1_mode ≤ (0 : Int)) (c1_mode ≥ (0 : Int)) (c1_level ≤ (0 : Int)) (c1_level ≥ (0 : Int)) (c1_group ≤ (0 : Int)) (c1_group ≥ (0 : Int)) (c1_depth ≥ (0 : Int)) (c1_node ≥ (0 : Int)) (c1_kind ≤ (1 : Int)) (c1_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) (c1_depth ≤ (0 : Int)) (c1_node ≤ (0 : Int)) ((h + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)) (c1_sign ≤ (2 : Int)) (c1_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2902 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (formula_1374 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h) := by
  exact (Or.elim (replay_2901 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_2898 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182 i158) t0))))

-- Checked replay of unit-resolution.
theorem replay_2903 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i181 : (formula_1366 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (¬ (formula_1361 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) := by
  exact (Or.elim (replay_2811 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h i181) (fun l0 => (False.elim (l0 (replay_2900 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182 i158)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_2902 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i182 i158)))))))

-- Checked replay of unit-resolution.
theorem replay_2904 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i181 : (formula_1366 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_2799 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h) (fun l0 => (False.elim ((replay_2903 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i181 i182 i158) l0))) (fun t0 => t0))

abbrev shared_expr_Repair051_92 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_1444 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (shared_expr_Repair051_92 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)

abbrev shared_expr_Repair051_93 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((¬ (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ∨ (¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_1445 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (shared_expr_Repair051_93 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)

theorem propositional_1218 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ p2)) ∨ (¬ p0) ∨ (¬ p1) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2905 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (formula_1445 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := by
  exact (propositional_1218 (c1_kind ≤ (0 : Int)) (c1_kind ≥ (0 : Int)) ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))

theorem propositional_1219 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2906 (c1_kind : Int) : (((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))) ∨ (c1_kind ≥ (0 : Int))) := by
  exact (propositional_1219 (c1_kind ≤ (0 : Int)) (c1_kind ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2907 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (c1_kind ≥ (0 : Int)) := by
  exact (Or.elim (replay_2906 c1_kind) (fun l0 => (False.elim ((replay_2896 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182 i158) l0))) (fun t0 => t0))

abbrev shared_expr_Repair051_94 (c0_node c1_node : Int) : Prop := (((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev shared_expr_Repair051_95 (c0_node c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev formula_1446 (c0_node c1_node c1_sign : Int) : Prop := ((shared_expr_Repair051_94 c0_node c1_node) ∨ (shared_expr_Repair051_95 c0_node c1_node c1_sign))

abbrev shared_expr_Repair051_96 (c0_node c1_node : Int) : Prop := (((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))
abbrev shared_expr_Repair051_97 (c0_node c0_sign c1_node : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))))
abbrev formula_1447 (c0_node c0_sign c1_node : Int) : Prop := ((shared_expr_Repair051_96 c0_node c1_node) ∨ (shared_expr_Repair051_97 c0_node c0_sign c1_node))

abbrev shared_expr_Repair051_98 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ∨ (formula_1446 c0_node c1_node c1_sign)))
abbrev shared_expr_Repair051_99 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((shared_expr_Repair051_98 c0_depth c0_node c1_depth c1_node c1_sign) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))))) ∧ (formula_1447 c0_node c0_sign c1_node)))
abbrev formula_1448 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_99 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Repair051_100 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair051_101 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ∨ (shared_expr_Repair051_100 c0_node c0_sign c1_node c1_sign))
abbrev formula_1449 (c0_node c0_sign c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_101 c0_node c0_sign c1_node c1_sign)

abbrev shared_expr_Repair051_102 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) ∧ (formula_1448 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ∧ (formula_1449 c0_node c0_sign c1_node c1_sign)))
abbrev formula_1450 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_102 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Repair051_103 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) ∧ (¬ ((¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ∨ (¬ (formula_1450 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))))) ∨ ((¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))))
abbrev formula_1451 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_103 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Repair051_104 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∧ (¬ ((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∨ (¬ (formula_1451 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))))
abbrev shared_expr_Repair051_105 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((shared_expr_Repair051_104 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ∨ ((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∧ (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)))
abbrev formula_1452 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_105 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

abbrev shared_expr_Repair051_106 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∨ (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (¬ (formula_1452 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)))
abbrev formula_1453 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_106 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

theorem propositional_1220 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Prop) : (p0 ∨ p1 ∨ (¬ ((p0 ∧ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((((¬ p4) ∨ (¬ p5)) ∧ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((((¬ p8) ∨ (¬ p9)) ∧ ((((¬ p10) ∨ (¬ p11)) ∧ ((¬ p12) ∨ (¬ p13) ∨ ((((¬ p14) ∨ (¬ p15)) ∧ (¬ p14)) ∨ ((¬ ((¬ p14) ∨ (¬ p15))) ∧ (¬ ((¬ p16) ∨ (¬ p17))))))) ∨ ((¬ ((¬ p10) ∨ (¬ p11))) ∧ ((((¬ p18) ∨ (¬ p19)) ∧ (¬ p19)) ∨ ((¬ ((¬ p18) ∨ (¬ p19))) ∧ (¬ ((¬ p20) ∨ (¬ p21)))))))) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ ((((¬ p22) ∨ (¬ p23)) ∧ (¬ p23)) ∨ ((¬ ((¬ p22) ∨ (¬ p23))) ∧ (¬ ((¬ p20) ∨ (¬ p21) ∨ (¬ p16) ∨ (¬ p17))))))))))) ∨ ((¬ ((¬ p4) ∨ (¬ p5))) ∧ (¬ ((¬ p24) ∨ (¬ p25))))))))) ∨ ((¬ p0) ∧ p1)))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2908 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1453 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact (propositional_1220 ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (c1_kind ≤ (0 : Int)) (c1_kind ≥ (0 : Int)) (c0_kind ≤ (2 : Int)) (c0_kind ≥ (2 : Int)) (c1_kind ≤ (2 : Int)) (c1_kind ≥ (2 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)) ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) (c1_kind ≤ (1 : Int)) (c1_kind ≥ (1 : Int)))

abbrev shared_expr_Repair051_107 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((¬ (¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))))) ∧ (((c0_level ≠ c1_level) ∧ (c0_level < c1_level)) ∨ ((¬ (c0_level ≠ c1_level)) ∧ (((c0_mode ≠ c1_mode) ∧ (c0_mode < c1_mode)) ∨ ((¬ (c0_mode ≠ c1_mode)) ∧ (c0_group < c1_group))))))
abbrev formula_1454 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))) ∨ (shared_expr_Repair051_107 c0_group c0_level c0_mode c1_group c1_level c1_mode))

abbrev shared_expr_Repair051_108 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((((c1_depth + (1 : Int)) = c0_depth) ∧ (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ ((c0_node / (2 : Int)) < c1_node)))) ∨ ((¬ ((c1_depth + (1 : Int)) = c0_depth)) ∧ True))
abbrev formula_1455 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_108 c0_depth c0_node c1_depth c1_node c1_sign)

abbrev shared_expr_Repair051_109 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((((c0_depth + (1 : Int)) = c1_depth) ∧ (((c0_node = (c1_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c1_node / (2 : Int)))) ∧ (c0_node < (c1_node / (2 : Int)))))) ∨ ((¬ ((c0_depth + (1 : Int)) = c1_depth)) ∧ (formula_1455 c0_depth c0_node c1_depth c1_node c1_sign)))
abbrev formula_1456 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_109 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Repair051_110 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((c0_depth = c1_depth) ∧ (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (c0_node < c1_node)))) ∨ ((¬ (c0_depth = c1_depth)) ∧ (formula_1456 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev formula_1457 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_110 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Repair051_111 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((c0_kind = (2 : Int)) ∧ (True ∧ (c1_kind = (1 : Int)))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ (((c1_kind = (2 : Int)) ∧ False) ∨ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1457 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev formula_1458 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_111 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Repair051_112 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ (((c1_kind = (0 : Int)) ∧ (formula_1454 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ (c1_kind = (0 : Int))) ∧ True))) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (((c1_kind = (0 : Int)) ∧ False) ∨ ((¬ (c1_kind = (0 : Int))) ∧ (formula_1458 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))))
abbrev formula_1459 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_112 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

abbrev shared_expr_Repair051_113 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (((c0_level = c1_level) ∧ (((c0_mode = c1_mode) ∧ (¬ (c1_group ≤ c0_group))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ (c1_mode ≤ c0_mode))))) ∨ ((¬ (c0_level = c1_level)) ∧ (¬ (c1_level ≤ c0_level)))))
abbrev formula_1460 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((shared_expr_Repair051_113 c0_group c0_level c0_mode c1_group c1_level c1_mode) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))

abbrev shared_expr_Repair051_114 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (c0_depth = ((-1 : Int) + c1_depth))) ∧ ((¬ (c1_depth = ((-1 : Int) + c0_depth))) ∨ (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ (¬ (c1_node ≤ (c0_node / (2 : Int))))))))
abbrev shared_expr_Repair051_115 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((c0_depth = ((-1 : Int) + c1_depth)) ∧ (((c0_node = (c1_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c1_node / (2 : Int)))) ∧ (¬ ((c1_node / (2 : Int)) ≤ c0_node))))) ∨ (shared_expr_Repair051_114 c0_depth c0_node c1_depth c1_node c1_sign))
abbrev formula_1461 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_115 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Repair051_116 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((c0_depth = c1_depth) ∧ (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ (c1_node ≤ c0_node))))) ∨ ((¬ (c0_depth = c1_depth)) ∧ (formula_1461 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev formula_1462 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_116 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Repair051_117 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (c1_kind = (0 : Int))) ∧ (((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1462 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev formula_1463 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_117 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Repair051_118 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ ((¬ (c1_kind = (0 : Int))) ∨ (formula_1460 c0_group c0_level c0_mode c1_group c1_level c1_mode))) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (formula_1463 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
abbrev formula_1464 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_118 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

abbrev shared_expr_Repair051_119 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (formula_1464 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
abbrev formula_1465 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Repair051_119 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

theorem normalized_1221 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 : Prop) : (((p0 ∧ ((p1 ∧ (((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2)) ∨ ((¬ (¬ ((¬ p2) ↔ (¬ p3)))) ∧ (((¬ p4) ∧ p5) ∨ ((¬ (¬ p4)) ∧ (((¬ p6) ∧ p7) ∨ ((¬ (¬ p6)) ∧ p8))))))) ∨ ((¬ p1) ∧ True))) ∨ ((¬ p0) ∧ ((p1 ∧ False) ∨ ((¬ p1) ∧ ((p9 ∧ (True ∧ p10)) ∨ ((¬ p9) ∧ ((p11 ∧ False) ∨ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ p15))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((p18 ∧ ((p19 ∧ p20) ∨ ((¬ p19) ∧ p21))) ∨ ((¬ p18) ∧ True)))))))))))))) ↔ ((p0 ∧ ((¬ p1) ∨ ((((¬ p2) ↔ (¬ p3)) ∧ ((p4 ∧ ((p6 ∧ (¬ (¬ p8))) ∨ ((¬ p6) ∧ (¬ (¬ p7))))) ∨ ((¬ p4) ∧ (¬ (¬ p5))))) ∨ ((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2))))) ∨ ((¬ p0) ∧ ((¬ p1) ∧ ((p9 ∧ p10) ∨ ((¬ p9) ∧ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ (¬ (¬ p15))))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((¬ p18) ∨ ((p19 ∧ p20) ∨ ((¬ p19) ∧ (¬ (¬ p21)))))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5104 (c0_mode c1_mode : Int) : (¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ↔ (¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) := (not_congr (iff_congr (normalization_693 c0_mode) (normalization_2160 c1_mode)))

theorem normalization_5105 (c0_level c1_level : Int) : (c0_level ≠ c1_level) ↔ (¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_5106 (c0_level c1_level : Int) : (c0_level < c1_level) ↔ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5107 (c0_mode c1_mode : Int) : (c0_mode ≠ c1_mode) ↔ (¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_5108 (c0_mode c1_mode : Int) : (c0_mode < c1_mode) ↔ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5109 (c0_group c1_group : Int) : (c0_group < c1_group) ↔ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair051_120 (c0_group c0_mode c1_group c1_mode : Int) : Prop := (((¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∧ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))))) ∧ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))))
theorem normalization_5110 (c0_group c0_mode c1_group c1_mode : Int) : (((c0_mode ≠ c1_mode) ∧ (c0_mode < c1_mode)) ∨ ((¬ (c0_mode ≠ c1_mode)) ∧ (c0_group < c1_group))) ↔ (shared_expr_Repair051_120 c0_group c0_mode c1_group c1_mode) := (or_congr (and_congr (normalization_5107 c0_mode c1_mode) (normalization_5108 c0_mode c1_mode)) (and_congr (not_congr (normalization_5107 c0_mode c1_mode)) (normalization_5109 c0_group c1_group)))

abbrev shared_expr_Repair051_121 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∧ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair051_120 c0_group c0_mode c1_group c1_mode)))
theorem normalization_5111 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (((c0_level ≠ c1_level) ∧ (c0_level < c1_level)) ∨ ((¬ (c0_level ≠ c1_level)) ∧ (((c0_mode ≠ c1_mode) ∧ (c0_mode < c1_mode)) ∨ ((¬ (c0_mode ≠ c1_mode)) ∧ (c0_group < c1_group))))) ↔ (shared_expr_Repair051_121 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_5105 c0_level c1_level) (normalization_5106 c0_level c1_level)) (and_congr (not_congr (normalization_5105 c0_level c1_level)) (normalization_5110 c0_group c0_mode c1_group c1_mode)))

abbrev shared_expr_Repair051_122 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))) ∨ ((¬ (¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair051_121 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
theorem normalization_5112 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1454 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Repair051_122 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_5104 c0_mode c1_mode) (normalization_693 c0_mode)) (and_congr (not_congr (normalization_5104 c0_mode c1_mode)) (normalization_5111 c0_group c0_level c0_mode c1_group c1_level c1_mode)))

abbrev shared_expr_Repair051_123 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair051_122 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ True))
theorem normalization_5113 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (((c1_kind = (0 : Int)) ∧ (formula_1454 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ (c1_kind = (0 : Int))) ∧ True)) ↔ (shared_expr_Repair051_123 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := (or_congr (and_congr (normalization_1439 c1_kind) (normalization_5112 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (and_congr (not_congr (normalization_1439 c1_kind)) (normalization_305)))

theorem normalization_5114 (c1_kind : Int) : (True ∧ (c1_kind = (1 : Int))) ↔ (True ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) := (and_congr (normalization_305) (normalization_1447 c1_kind))

theorem normalization_5115 (c0_depth c1_depth : Int) : (c0_depth = c1_depth) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_5116 (c0_node c1_node : Int) : (c0_node = c1_node) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_5117 (c0_sign c1_sign : Int) : ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) := (and_congr (normalization_144 c0_sign) (normalization_1456 c1_sign))

theorem normalization_5118 (c0_node c1_node : Int) : (c0_node < c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair051_124 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair051_125 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Repair051_124 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
theorem normalization_5119 (c0_node c0_sign c1_node c1_sign : Int) : (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (c0_node < c1_node))) ↔ (shared_expr_Repair051_125 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_5116 c0_node c1_node) (normalization_5117 c0_sign c1_sign)) (and_congr (not_congr (normalization_5116 c0_node c1_node)) (normalization_5118 c0_node c1_node)))

theorem normalization_5120 (c0_depth c1_depth : Int) : ((c0_depth + (1 : Int)) = c1_depth) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_5121 (c0_node c1_node : Int) : (c0_node = (c1_node / (2 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_5122 (c0_node c1_node : Int) : (c0_node < (c1_node / (2 : Int))) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

abbrev shared_expr_Repair051_126 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair051_127 (c0_node c0_sign c1_node : Int) : Prop := ((((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair051_126 c0_node c1_node))
theorem normalization_5123 (c0_node c0_sign c1_node : Int) : (((c0_node = (c1_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c1_node / (2 : Int)))) ∧ (c0_node < (c1_node / (2 : Int))))) ↔ (shared_expr_Repair051_127 c0_node c0_sign c1_node) := (or_congr (and_congr (normalization_5121 c0_node c1_node) (normalization_144 c0_sign)) (and_congr (not_congr (normalization_5121 c0_node c1_node)) (normalization_5122 c0_node c1_node)))

theorem normalization_5124 (c0_depth c1_depth : Int) : ((c1_depth + (1 : Int)) = c0_depth) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_5125 (c0_node c1_node : Int) : (c1_node = (c0_node / (2 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_5126 (c0_node c1_node : Int) : ((c0_node / (2 : Int)) < c1_node) ↔ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair051_128 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
abbrev shared_expr_Repair051_129 (c0_node c1_node c1_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_128 c0_node c1_node))
theorem normalization_5127 (c0_node c1_node c1_sign : Int) : (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ ((c0_node / (2 : Int)) < c1_node))) ↔ (shared_expr_Repair051_129 c0_node c1_node c1_sign) := (or_congr (and_congr (normalization_5125 c0_node c1_node) (normalization_1456 c1_sign)) (and_congr (not_congr (normalization_5125 c0_node c1_node)) (normalization_5126 c0_node c1_node)))

abbrev shared_expr_Repair051_130 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∧ (shared_expr_Repair051_129 c0_node c1_node c1_sign)) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) ∧ True))
theorem normalization_5128 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (formula_1455 c0_depth c0_node c1_depth c1_node c1_sign) ↔ (shared_expr_Repair051_130 c0_depth c0_node c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5124 c0_depth c1_depth) (normalization_5127 c0_node c1_node c1_sign)) (and_congr (not_congr (normalization_5124 c0_depth c1_depth)) (normalization_305)))

abbrev shared_expr_Repair051_131 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair051_127 c0_node c0_sign c1_node)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair051_130 c0_depth c0_node c1_depth c1_node c1_sign)))
theorem normalization_5129 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1456 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Repair051_131 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5120 c0_depth c1_depth) (normalization_5123 c0_node c0_sign c1_node)) (and_congr (not_congr (normalization_5120 c0_depth c1_depth)) (normalization_5128 c0_depth c0_node c1_depth c1_node c1_sign)))

abbrev shared_expr_Repair051_132 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair051_125 c0_node c0_sign c1_node c1_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_131 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
theorem normalization_5130 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1457 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Repair051_132 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5115 c0_depth c1_depth) (normalization_5119 c0_node c0_sign c1_node c1_sign)) (and_congr (not_congr (normalization_5115 c0_depth c1_depth)) (normalization_5129 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

abbrev shared_expr_Repair051_133 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ∧ False) ∨ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_132 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
theorem normalization_5131 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((c1_kind = (2 : Int)) ∧ False) ∨ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1457 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))) ↔ (shared_expr_Repair051_133 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_1446 c1_kind) (normalization_1253)) (and_congr (not_congr (normalization_1446 c1_kind)) (normalization_5130 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

abbrev shared_expr_Repair051_134 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (True ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))))) ∨ ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_133 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_5132 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1458 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Repair051_134 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_141 c0_kind) (normalization_5114 c1_kind)) (and_congr (not_congr (normalization_141 c0_kind)) (normalization_5131 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Repair051_135 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ False) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_134 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_5133 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((c1_kind = (0 : Int)) ∧ False) ∨ ((¬ (c1_kind = (0 : Int))) ∧ (formula_1458 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))) ↔ (shared_expr_Repair051_135 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_1439 c1_kind) (normalization_1253)) (and_congr (not_congr (normalization_1439 c1_kind)) (normalization_5132 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Repair051_136 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair051_123 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_135 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_5134 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Repair051_136 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (or_congr (and_congr (normalization_134 c0_kind) (normalization_5113 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (and_congr (not_congr (normalization_134 c0_kind)) (normalization_5133 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

theorem normalization_5135 (c1_kind : Int) : (¬ (c1_kind = (0 : Int))) ↔ (¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) := (not_congr (normalization_1439 c1_kind))

theorem normalization_5136 (c0_mode c1_mode : Int) : ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ↔ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) := (iff_congr (normalization_693 c0_mode) (normalization_2160 c1_mode))

theorem normalization_5137 (c0_level c1_level : Int) : (c0_level = c1_level) ↔ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_5138 (c0_mode c1_mode : Int) : (c0_mode = c1_mode) ↔ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_5139 (c0_group c1_group : Int) : (c1_group ≤ c0_group) ↔ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5140 (c0_group c1_group : Int) : (¬ (c1_group ≤ c0_group)) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_5139 c0_group c1_group))

theorem normalization_5141 (c0_mode c1_mode : Int) : (c1_mode ≤ c0_mode) ↔ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5142 (c0_mode c1_mode : Int) : (¬ (c1_mode ≤ c0_mode)) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_5141 c0_mode c1_mode))

abbrev shared_expr_Repair051_137 (c0_group c0_mode c1_group c1_mode : Int) : Prop := (((((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))))
theorem normalization_5143 (c0_group c0_mode c1_group c1_mode : Int) : (((c0_mode = c1_mode) ∧ (¬ (c1_group ≤ c0_group))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ (c1_mode ≤ c0_mode)))) ↔ (shared_expr_Repair051_137 c0_group c0_mode c1_group c1_mode) := (or_congr (and_congr (normalization_5138 c0_mode c1_mode) (normalization_5140 c0_group c1_group)) (and_congr (not_congr (normalization_5138 c0_mode c1_mode)) (normalization_5142 c0_mode c1_mode)))

theorem normalization_5144 (c0_level c1_level : Int) : (c1_level ≤ c0_level) ↔ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5145 (c0_level c1_level : Int) : (¬ (c1_level ≤ c0_level)) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5144 c0_level c1_level))

abbrev shared_expr_Repair051_138 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair051_137 c0_group c0_mode c1_group c1_mode)) ∨ ((¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))))
theorem normalization_5146 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (((c0_level = c1_level) ∧ (((c0_mode = c1_mode) ∧ (¬ (c1_group ≤ c0_group))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ (c1_mode ≤ c0_mode))))) ∨ ((¬ (c0_level = c1_level)) ∧ (¬ (c1_level ≤ c0_level)))) ↔ (shared_expr_Repair051_138 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_5137 c0_level c1_level) (normalization_5143 c0_group c0_mode c1_group c1_mode)) (and_congr (not_congr (normalization_5137 c0_level c1_level)) (normalization_5145 c0_level c1_level)))

abbrev shared_expr_Repair051_139 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair051_138 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_5147 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1460 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Repair051_139 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_5136 c0_mode c1_mode) (normalization_5146 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (and_congr (not_congr (normalization_5136 c0_mode c1_mode)) (normalization_693 c0_mode)))

theorem normalization_5148 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((¬ (c1_kind = (0 : Int))) ∨ (formula_1460 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair051_139 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (or_congr (normalization_5135 c1_kind) (normalization_5147 c0_group c0_level c0_mode c1_group c1_level c1_mode))

theorem normalization_5149 (c1_kind : Int) : (¬ (c1_kind = (2 : Int))) ↔ (¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) := (not_congr (normalization_1446 c1_kind))

theorem normalization_5150 (c0_node c1_node : Int) : (c1_node ≤ c0_node) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5151 (c0_node c1_node : Int) : (¬ (c1_node ≤ c0_node)) ↔ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5150 c0_node c1_node))

abbrev shared_expr_Repair051_140 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Repair051_124 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))))
theorem normalization_5152 (c0_node c0_sign c1_node c1_sign : Int) : (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ (c1_node ≤ c0_node)))) ↔ (shared_expr_Repair051_140 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_5116 c0_node c1_node) (normalization_5117 c0_sign c1_sign)) (and_congr (not_congr (normalization_5116 c0_node c1_node)) (normalization_5151 c0_node c1_node)))

theorem normalization_5153 (c0_depth c1_depth : Int) : (c0_depth = ((-1 : Int) + c1_depth)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_5154 (c0_node c1_node : Int) : ((c1_node / (2 : Int)) ≤ c0_node) ↔ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5155 (c0_node c1_node : Int) : (¬ ((c1_node / (2 : Int)) ≤ c0_node)) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (not_congr (normalization_5154 c0_node c1_node))

theorem normalization_5156 (c0_node c0_sign c1_node : Int) : (((c0_node = (c1_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c1_node / (2 : Int)))) ∧ (¬ ((c1_node / (2 : Int)) ≤ c0_node)))) ↔ (shared_expr_Repair051_127 c0_node c0_sign c1_node) := (or_congr (and_congr (normalization_5121 c0_node c1_node) (normalization_144 c0_sign)) (and_congr (not_congr (normalization_5121 c0_node c1_node)) (normalization_5155 c0_node c1_node)))

theorem normalization_5157 (c0_depth c1_depth : Int) : (c1_depth = ((-1 : Int) + c0_depth)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_5158 (c0_depth c1_depth : Int) : (¬ (c1_depth = ((-1 : Int) + c0_depth))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) := (not_congr (normalization_5157 c0_depth c1_depth))

theorem normalization_5159 (c0_node c1_node : Int) : (c1_node ≤ (c0_node / (2 : Int))) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5160 (c0_node c1_node : Int) : (¬ (c1_node ≤ (c0_node / (2 : Int)))) ↔ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5159 c0_node c1_node))

abbrev shared_expr_Repair051_141 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair051_142 (c0_node c1_node c1_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_141 c0_node c1_node))
theorem normalization_5161 (c0_node c1_node c1_sign : Int) : (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ (¬ (c1_node ≤ (c0_node / (2 : Int)))))) ↔ (shared_expr_Repair051_142 c0_node c1_node c1_sign) := (or_congr (and_congr (normalization_5125 c0_node c1_node) (normalization_1456 c1_sign)) (and_congr (not_congr (normalization_5125 c0_node c1_node)) (normalization_5160 c0_node c1_node)))

theorem normalization_5162 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : ((¬ (c1_depth = ((-1 : Int) + c0_depth))) ∨ (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ (¬ (c1_node ≤ (c0_node / (2 : Int))))))) ↔ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair051_142 c0_node c1_node c1_sign)) := (or_congr (normalization_5158 c0_depth c1_depth) (normalization_5161 c0_node c1_node c1_sign))

abbrev shared_expr_Repair051_143 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair051_142 c0_node c1_node c1_sign)))
abbrev shared_expr_Repair051_144 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair051_127 c0_node c0_sign c1_node)) ∨ (shared_expr_Repair051_143 c0_depth c0_node c1_depth c1_node c1_sign))
theorem normalization_5163 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1461 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Repair051_144 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5153 c0_depth c1_depth) (normalization_5156 c0_node c0_sign c1_node)) (and_congr (not_congr (normalization_5153 c0_depth c1_depth)) (normalization_5162 c0_depth c0_node c1_depth c1_node c1_sign)))

abbrev shared_expr_Repair051_145 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair051_140 c0_node c0_sign c1_node c1_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_144 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
theorem normalization_5164 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1462 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Repair051_145 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5115 c0_depth c1_depth) (normalization_5152 c0_node c0_sign c1_node c1_sign)) (and_congr (not_congr (normalization_5115 c0_depth c1_depth)) (normalization_5163 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

theorem normalization_5165 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : ((¬ (c1_kind = (2 : Int))) ∧ (formula_1462 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_145 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (and_congr (normalization_5149 c1_kind) (normalization_5164 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

abbrev shared_expr_Repair051_146 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair051_145 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev shared_expr_Repair051_147 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair051_146 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_5166 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1462 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))) ↔ (shared_expr_Repair051_147 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_141 c0_kind) (normalization_1447 c1_kind)) (and_congr (not_congr (normalization_141 c0_kind)) (normalization_5165 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

theorem normalization_5167 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1463 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_147 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) := (and_congr (normalization_5135 c1_kind) (normalization_5166 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

abbrev shared_expr_Repair051_148 (c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair051_139 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
abbrev shared_expr_Repair051_149 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair051_147 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_5168 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1464 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ ((shared_expr_Repair051_148 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Repair051_149 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) := (or_congr (and_congr (normalization_134 c0_kind) (normalization_5148 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (and_congr (not_congr (normalization_134 c0_kind)) (normalization_5167 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Repair051_150 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((shared_expr_Repair051_136 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ ((shared_expr_Repair051_148 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Repair051_149 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_5169 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1465 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Repair051_150 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (iff_congr (normalization_5134 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (normalization_5168 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2909 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1465 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  classical
  have ht := (normalized_1221 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((c0_mode) ≤ (3 : Int)) ((c1_mode) ≤ (3 : Int)) (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) (shared_expr_Repair051_127 c0_node c0_sign c1_node) ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5169 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) hn

end H4Formal.Generated.Repair
