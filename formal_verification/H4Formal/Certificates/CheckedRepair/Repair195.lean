import H4Formal.Certificates.CheckedRepair.Repair194

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_2926 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_0 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))))
theorem normalization_8988 (c0_depth c3_depth : Int) : (((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair195_0 c0_depth c3_depth) := (iff_congr (normalization_8975 c0_depth c3_depth) (normalization_8986 c0_depth c3_depth))

-- Checked replay of trans.
abbrev shared_expr_Repair195_1 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
theorem replay_15395 (c0_depth c3_depth : Int) : (((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2926 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Repair195_0 c0_depth c3_depth))
  have n0 : (shared_expr_Repair195_1 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8982 c0_depth c3_depth) (replay_15393 c0_depth c3_depth)
  have n1 : (shared_expr_Repair195_0 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8987 c0_depth c3_depth) (replay_15394 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8988 c0_depth c3_depth) hn

theorem normalized_2927 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8989 (c0_depth c3_depth : Int) : ((c0_depth = c3_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair195_0 c0_depth c3_depth) := (iff_congr (normalization_8872 c0_depth c3_depth) (normalization_8986 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_15396 (c0_depth c3_depth : Int) : ((c0_depth = c3_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2927 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Repair195_0 c0_depth c3_depth))
  have n0 : (shared_expr_Repair195_1 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8976 c0_depth c3_depth) (replay_15390 c0_depth c3_depth)
  have n1 : (shared_expr_Repair195_0 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8988 c0_depth c3_depth) (replay_15395 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8989 c0_depth c3_depth) hn

theorem normalized_2928 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8990 (c0_node c3_node : Int) : (c0_node ≤ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_8991 (c0_node c3_node : Int) : (c0_node ≥ c3_node) ↔ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8992 (c0_node c3_node : Int) : ((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_8990 c0_node c3_node) (normalization_8991 c0_node c3_node))

abbrev shared_expr_Repair195_2 (c0_node c3_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_8993 (c0_node c3_node : Int) : ((c0_node = c3_node) ↔ ((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node))) ↔ (shared_expr_Repair195_2 c0_node c3_node) := (iff_congr (normalization_8873 c0_node c3_node) (normalization_8992 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_15397 (c0_node c3_node : Int) : ((c0_node = c3_node) ↔ ((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node))) := by
  classical
  have ht := (normalized_2928 (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8993 c0_node c3_node) hn

theorem normalized_2929 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8994 (c0_node c3_node : Int) : ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_8995 (c0_node c3_node : Int) : ((c0_node ≤ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (iff_congr (normalization_8990 c0_node c3_node) (normalization_8994 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_15398 (c0_node c3_node : Int) : ((c0_node ≤ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2929 ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8995 c0_node c3_node) hn

theorem normalized_2930 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8996 (c0_node c3_node : Int) : ((c0_node ≥ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_8991 c0_node c3_node) (normalization_8936 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_15399 (c0_node c3_node : Int) : ((c0_node ≥ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2930 ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8996 c0_node c3_node) hn

theorem normalized_2931 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8997 (c0_node c3_node : Int) : (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_8994 c0_node c3_node) (normalization_8936 c0_node c3_node))

theorem normalization_8998 (c0_node c3_node : Int) : (((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair195_2 c0_node c3_node) := (iff_congr (normalization_8992 c0_node c3_node) (normalization_8997 c0_node c3_node))

-- Checked replay of monotonicity.
theorem replay_15400 (c0_node c3_node : Int) : (((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2931 ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have n0 : (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8995 c0_node c3_node) (replay_15398 c0_node c3_node)
  have n1 : ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8996 c0_node c3_node) (replay_15399 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8998 c0_node c3_node) hn

abbrev shared_expr_Repair195_3 (c0_node c3_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))))
abbrev formula_3616 (c0_node c3_node : Int) : Prop := (shared_expr_Repair195_3 c0_node c3_node)

theorem normalized_2932 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8999 (c0_node c3_node : Int) : (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_8994 c0_node c3_node))

theorem normalization_9000 (c0_node c3_node : Int) : ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_8999 c0_node c3_node) (normalization_8937 c0_node c3_node))

theorem normalization_9001 (c0_node c3_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_9000 c0_node c3_node))

abbrev shared_expr_Repair195_4 (c0_node c3_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))))
theorem normalization_9002 (c0_node c3_node : Int) : (formula_3616 c0_node c3_node) ↔ (shared_expr_Repair195_4 c0_node c3_node) := (iff_congr (normalization_8997 c0_node c3_node) (normalization_9001 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_15401 (c0_node c3_node : Int) : (formula_3616 c0_node c3_node) := by
  classical
  have ht := (normalized_2932 ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9002 c0_node c3_node) hn

theorem normalized_2933 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9003 (c0_node c3_node : Int) : (((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair195_4 c0_node c3_node) := (iff_congr (normalization_8992 c0_node c3_node) (normalization_9001 c0_node c3_node))

-- Checked replay of trans.
theorem replay_15402 (c0_node c3_node : Int) : (((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2933 (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Repair195_4 c0_node c3_node))
  have n0 : (shared_expr_Repair195_2 c0_node c3_node) := by
    exact Iff.mp (normalization_8998 c0_node c3_node) (replay_15400 c0_node c3_node)
  have n1 : (shared_expr_Repair195_4 c0_node c3_node) := by
    exact Iff.mp (normalization_9002 c0_node c3_node) (replay_15401 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9003 c0_node c3_node) hn

theorem normalized_2934 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9004 (c0_node c3_node : Int) : ((c0_node = c3_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair195_4 c0_node c3_node) := (iff_congr (normalization_8873 c0_node c3_node) (normalization_9001 c0_node c3_node))

-- Checked replay of trans.
theorem replay_15403 (c0_node c3_node : Int) : ((c0_node = c3_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2934 (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Repair195_4 c0_node c3_node))
  have n0 : (shared_expr_Repair195_2 c0_node c3_node) := by
    exact Iff.mp (normalization_8993 c0_node c3_node) (replay_15397 c0_node c3_node)
  have n1 : (shared_expr_Repair195_4 c0_node c3_node) := by
    exact Iff.mp (normalization_9003 c0_node c3_node) (replay_15402 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9004 c0_node c3_node) hn

theorem normalized_2935 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9005 (c0_sign c3_sign : Int) : ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (and_congr (normalization_461 c0_sign) (normalization_6992 c3_sign))

abbrev shared_expr_Repair195_5 (c0_sign c3_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))))
theorem normalization_9006 (c0_sign c3_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) ↔ (shared_expr_Repair195_5 c0_sign c3_sign) := (iff_congr (normalization_8874 c0_sign c3_sign) (normalization_9005 c0_sign c3_sign))

-- Checked replay of monotonicity.
theorem replay_15404 (c0_sign c3_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_2935 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3117 c0_sign) (replay_2177 c0_sign)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6994 c3_sign) (replay_6142 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9006 c0_sign c3_sign) hn

abbrev shared_expr_Repair195_6 (c0_sign c3_sign : Int) : Prop := (((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev formula_3617 (c0_sign c3_sign : Int) : Prop := (shared_expr_Repair195_6 c0_sign c3_sign)

theorem normalized_2936 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9007 (c0_sign c3_sign : Int) : ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ↔ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) := (or_congr (normalization_457 c0_sign) (or_congr (normalization_459 c0_sign) (or_congr (normalization_6989 c3_sign) (normalization_6990 c3_sign))))

theorem normalization_9008 (c0_sign c3_sign : Int) : (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_9007 c0_sign c3_sign))

abbrev shared_expr_Repair195_7 (c0_sign c3_sign : Int) : Prop := (((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_9009 (c0_sign c3_sign : Int) : (formula_3617 c0_sign c3_sign) ↔ (shared_expr_Repair195_7 c0_sign c3_sign) := (iff_congr (normalization_9005 c0_sign c3_sign) (normalization_9008 c0_sign c3_sign))

-- Checked replay of rewrite.
theorem replay_15405 (c0_sign c3_sign : Int) : (formula_3617 c0_sign c3_sign) := by
  classical
  have ht := (normalized_2936 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9009 c0_sign c3_sign) hn

theorem normalized_2937 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_8 (c0_sign c3_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_9010 (c0_sign c3_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (shared_expr_Repair195_8 c0_sign c3_sign) := (iff_congr (normalization_8874 c0_sign c3_sign) (normalization_9008 c0_sign c3_sign))

-- Checked replay of trans.
theorem replay_15406 (c0_sign c3_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2937 ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair195_5 c0_sign c3_sign) := by
    exact Iff.mp (normalization_9006 c0_sign c3_sign) (replay_15404 c0_sign c3_sign)
  have n1 : (shared_expr_Repair195_7 c0_sign c3_sign) := by
    exact Iff.mp (normalization_9009 c0_sign c3_sign) (replay_15405 c0_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9010 c0_sign c3_sign) hn

abbrev shared_expr_Repair195_9 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair195_10 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Repair195_9 c0_node c0_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))
abbrev formula_3618 (c0_node c0_sign c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_10 c0_node c0_sign c3_node c3_sign)

abbrev shared_expr_Repair195_11 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((((c0_node = c3_node) ∧ ((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c0_node = c3_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_3618 c0_node c0_sign c3_node c3_sign))
abbrev formula_3619 (c0_node c0_sign c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_11 c0_node c0_sign c3_node c3_sign)

theorem normalized_2938 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_12 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair195_13 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Repair195_12 c0_node c0_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_9011 (c0_node c0_sign c3_node c3_sign : Int) : (formula_3618 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Repair195_13 c0_node c0_sign c3_node c3_sign) := (or_congr (and_congr (normalization_9001 c0_node c3_node) (normalization_9008 c0_sign c3_sign)) (and_congr (not_congr (normalization_9001 c0_node c3_node)) (normalization_8937 c0_node c3_node)))

abbrev shared_expr_Repair195_14 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair195_15 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Repair195_14 c0_node c0_sign c3_node c3_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_9012 (c0_node c0_sign c3_node c3_sign : Int) : (formula_3619 c0_node c0_sign c3_node c3_sign) ↔ ((shared_expr_Repair195_15 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Repair195_13 c0_node c0_sign c3_node c3_sign)) := (iff_congr (normalization_8938 c0_node c0_sign c3_node c3_sign) (normalization_9011 c0_node c0_sign c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_15407 (c0_node c0_sign c3_node c3_sign : Int) : (formula_3619 c0_node c0_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_2938 (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair195_4 c0_node c3_node) := by
    exact Iff.mp (normalization_9004 c0_node c3_node) (replay_15403 c0_node c3_node)
  have n1 : (shared_expr_Repair195_8 c0_sign c3_sign) := by
    exact Iff.mp (normalization_9010 c0_sign c3_sign) (replay_15406 c0_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9012 c0_node c0_sign c3_node c3_sign) hn

theorem normalized_2939 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_16 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair195_12 c0_node c0_sign c3_node c3_sign))
theorem normalization_9013 (c0_node c0_sign c3_node c3_sign : Int) : (formula_3581 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign) := (or_congr (and_congr (normalization_9000 c0_node c3_node) (normalization_8937 c0_node c3_node)) (and_congr (not_congr (normalization_9000 c0_node c3_node)) (normalization_9008 c0_sign c3_sign)))

theorem normalization_9014 (c0_node c0_sign c3_node c3_sign : Int) : ((formula_3618 c0_node c0_sign c3_node c3_sign) ↔ (formula_3581 c0_node c0_sign c3_node c3_sign)) ↔ ((shared_expr_Repair195_13 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign)) := (iff_congr (normalization_9011 c0_node c0_sign c3_node c3_sign) (normalization_9013 c0_node c0_sign c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_15408 (c0_node c0_sign c3_node c3_sign : Int) : ((formula_3618 c0_node c0_sign c3_node c3_sign) ↔ (formula_3581 c0_node c0_sign c3_node c3_sign)) := by
  classical
  have ht := (normalized_2939 ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9014 c0_node c0_sign c3_node c3_sign) hn

abbrev shared_expr_Repair195_17 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((((c0_node = c3_node) ∧ ((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c0_node = c3_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_3581 c0_node c0_sign c3_node c3_sign))
abbrev formula_3620 (c0_node c0_sign c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_17 c0_node c0_sign c3_node c3_sign)

theorem normalized_2940 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9015 (c0_node c0_sign c3_node c3_sign : Int) : (formula_3620 c0_node c0_sign c3_node c3_sign) ↔ ((shared_expr_Repair195_15 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign)) := (iff_congr (normalization_8938 c0_node c0_sign c3_node c3_sign) (normalization_9013 c0_node c0_sign c3_node c3_sign))

-- Checked replay of trans.
theorem replay_15409 (c0_node c0_sign c3_node c3_sign : Int) : (formula_3620 c0_node c0_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_2940 (shared_expr_Repair195_15 c0_node c0_sign c3_node c3_sign) (shared_expr_Repair195_13 c0_node c0_sign c3_node c3_sign) (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign))
  have n0 : ((shared_expr_Repair195_15 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Repair195_13 c0_node c0_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_9012 c0_node c0_sign c3_node c3_sign) (replay_15407 c0_node c0_sign c3_node c3_sign)
  have n1 : ((shared_expr_Repair195_13 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_9014 c0_node c0_sign c3_node c3_sign) (replay_15408 c0_node c0_sign c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9015 c0_node c0_sign c3_node c3_sign) hn

theorem normalized_2941 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9016 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_9017 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_9018 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_9016 c0_depth c3_depth) (normalization_9017 c0_depth c3_depth))

abbrev shared_expr_Repair195_18 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
theorem normalization_9019 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Repair195_18 c0_depth c3_depth) := (iff_congr (normalization_8939 c0_depth c3_depth) (normalization_9018 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_15410 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_2941 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_9019 c0_depth c3_depth) hn

abbrev shared_expr_Repair195_19 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))))
abbrev formula_3621 (c0_depth c3_depth : Int) : Prop := (shared_expr_Repair195_19 c0_depth c3_depth)

theorem normalized_2942 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9020 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := (not_congr (normalization_9016 c0_depth c3_depth))

theorem normalization_9021 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_9017 c0_depth c3_depth))

theorem normalization_9022 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_9020 c0_depth c3_depth) (normalization_9021 c0_depth c3_depth))

theorem normalization_9023 (c0_depth c3_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_9022 c0_depth c3_depth))

abbrev shared_expr_Repair195_20 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))))
theorem normalization_9024 (c0_depth c3_depth : Int) : (formula_3621 c0_depth c3_depth) ↔ (shared_expr_Repair195_20 c0_depth c3_depth) := (iff_congr (normalization_9018 c0_depth c3_depth) (normalization_9023 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_15411 (c0_depth c3_depth : Int) : (formula_3621 c0_depth c3_depth) := by
  classical
  have ht := (normalized_2942 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9024 c0_depth c3_depth) hn

theorem normalized_2943 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9025 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Repair195_20 c0_depth c3_depth) := (iff_congr (normalization_8939 c0_depth c3_depth) (normalization_9023 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_15412 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_2943 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Repair195_20 c0_depth c3_depth))
  have n0 : (shared_expr_Repair195_18 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9019 c0_depth c3_depth) (replay_15410 c0_depth c3_depth)
  have n1 : (shared_expr_Repair195_20 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9024 c0_depth c3_depth) (replay_15411 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9025 c0_depth c3_depth) hn

theorem normalized_2944 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9026 (c0_node c3_node : Int) : ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_9027 (c0_node c3_node : Int) : (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (and_congr (normalization_9026 c0_node c3_node) (normalization_8941 c0_node c3_node))

abbrev shared_expr_Repair195_21 (c0_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_9028 (c0_node c3_node : Int) : (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Repair195_21 c0_node c3_node) := (iff_congr (normalization_8940 c0_node c3_node) (normalization_9027 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_15413 (c0_node c3_node : Int) : (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2944 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_9028 c0_node c3_node) hn

abbrev shared_expr_Repair195_22 (c0_node c3_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_3622 (c0_node c3_node : Int) : Prop := (shared_expr_Repair195_22 c0_node c3_node)

theorem normalized_2945 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9029 (c0_node c3_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_9026 c0_node c3_node))

theorem normalization_9030 (c0_node c3_node : Int) : ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) := (or_congr (normalization_9029 c0_node c3_node) (normalization_8942 c0_node c3_node))

theorem normalization_9031 (c0_node c3_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) := (not_congr (normalization_9030 c0_node c3_node))

abbrev shared_expr_Repair195_23 (c0_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
theorem normalization_9032 (c0_node c3_node : Int) : (formula_3622 c0_node c3_node) ↔ (shared_expr_Repair195_23 c0_node c3_node) := (iff_congr (normalization_9027 c0_node c3_node) (normalization_9031 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_15414 (c0_node c3_node : Int) : (formula_3622 c0_node c3_node) := by
  classical
  have ht := (normalized_2945 (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)) (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9032 c0_node c3_node) hn

abbrev shared_expr_Repair195_24 (c0_node c3_node : Int) : Prop := (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_3623 (c0_node c3_node : Int) : Prop := (shared_expr_Repair195_24 c0_node c3_node)

theorem normalized_2946 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9033 (c0_node c3_node : Int) : (formula_3623 c0_node c3_node) ↔ (shared_expr_Repair195_23 c0_node c3_node) := (iff_congr (normalization_8940 c0_node c3_node) (normalization_9031 c0_node c3_node))

-- Checked replay of trans.
theorem replay_15415 (c0_node c3_node : Int) : (formula_3623 c0_node c3_node) := by
  classical
  have ht := (normalized_2946 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) (shared_expr_Repair195_23 c0_node c3_node))
  have n0 : (shared_expr_Repair195_21 c0_node c3_node) := by
    exact Iff.mp (normalization_9028 c0_node c3_node) (replay_15413 c0_node c3_node)
  have n1 : (shared_expr_Repair195_23 c0_node c3_node) := by
    exact Iff.mp (normalization_9032 c0_node c3_node) (replay_15414 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9033 c0_node c3_node) hn

abbrev shared_expr_Repair195_25 (c0_node c0_sign c3_node : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))))
abbrev shared_expr_Repair195_26 (c0_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_3624 (c0_node c0_sign c3_node : Int) : Prop := ((shared_expr_Repair195_25 c0_node c0_sign c3_node) ∨ (shared_expr_Repair195_26 c0_node c3_node))

theorem normalized_2947 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_27 (c0_node c0_sign c3_node : Int) : Prop := ((¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Repair195_28 (c0_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_9034 (c0_node c0_sign c3_node : Int) : (formula_3624 c0_node c0_sign c3_node) ↔ ((shared_expr_Repair195_27 c0_node c0_sign c3_node) ∨ (shared_expr_Repair195_28 c0_node c3_node)) := (or_congr (and_congr (normalization_9031 c0_node c3_node) (normalization_461 c0_sign)) (and_congr (not_congr (normalization_9031 c0_node c3_node)) (normalization_8942 c0_node c3_node)))

abbrev shared_expr_Repair195_29 (c0_node c3_node : Int) : Prop := ((¬ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair195_30 (c0_node c0_sign c3_node : Int) : Prop := ((((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair195_29 c0_node c3_node))
theorem normalization_9035 (c0_node c0_sign c3_node : Int) : ((formula_3606 c0_node c0_sign c3_node) ↔ (formula_3624 c0_node c0_sign c3_node)) ↔ ((shared_expr_Repair195_30 c0_node c0_sign c3_node) ↔ ((shared_expr_Repair195_27 c0_node c0_sign c3_node) ∨ (shared_expr_Repair195_28 c0_node c3_node))) := (iff_congr (normalization_8943 c0_node c0_sign c3_node) (normalization_9034 c0_node c0_sign c3_node))

-- Checked replay of monotonicity.
theorem replay_15416 (c0_node c0_sign c3_node : Int) : ((formula_3606 c0_node c0_sign c3_node) ↔ (formula_3624 c0_node c0_sign c3_node)) := by
  classical
  have ht := (normalized_2947 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Repair195_23 c0_node c3_node) := by
    exact Iff.mp (normalization_9033 c0_node c3_node) (replay_15415 c0_node c3_node)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3117 c0_sign) (replay_2177 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9035 c0_node c0_sign c3_node) hn

theorem normalized_2948 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_31 (c0_node c3_node : Int) : Prop := (((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_9036 (c0_node c0_sign c3_node : Int) : (formula_3579 c0_node c0_sign c3_node) ↔ ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node)) := (or_congr (and_congr (normalization_9030 c0_node c3_node) (normalization_8942 c0_node c3_node)) (and_congr (not_congr (normalization_9030 c0_node c3_node)) (normalization_461 c0_sign)))

theorem normalization_9037 (c0_node c0_sign c3_node : Int) : ((formula_3624 c0_node c0_sign c3_node) ↔ (formula_3579 c0_node c0_sign c3_node)) ↔ (((shared_expr_Repair195_27 c0_node c0_sign c3_node) ∨ (shared_expr_Repair195_28 c0_node c3_node)) ↔ ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node))) := (iff_congr (normalization_9034 c0_node c0_sign c3_node) (normalization_9036 c0_node c0_sign c3_node))

-- Checked replay of rewrite.
theorem replay_15417 (c0_node c0_sign c3_node : Int) : ((formula_3624 c0_node c0_sign c3_node) ↔ (formula_3579 c0_node c0_sign c3_node)) := by
  classical
  have ht := (normalized_2948 ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9037 c0_node c0_sign c3_node) hn

theorem normalized_2949 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9038 (c0_node c0_sign c3_node : Int) : ((formula_3606 c0_node c0_sign c3_node) ↔ (formula_3579 c0_node c0_sign c3_node)) ↔ ((shared_expr_Repair195_30 c0_node c0_sign c3_node) ↔ ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node))) := (iff_congr (normalization_8943 c0_node c0_sign c3_node) (normalization_9036 c0_node c0_sign c3_node))

-- Checked replay of trans.
theorem replay_15418 (c0_node c0_sign c3_node : Int) : ((formula_3606 c0_node c0_sign c3_node) ↔ (formula_3579 c0_node c0_sign c3_node)) := by
  classical
  have ht := (normalized_2949 (shared_expr_Repair195_30 c0_node c0_sign c3_node) ((shared_expr_Repair195_27 c0_node c0_sign c3_node) ∨ (shared_expr_Repair195_28 c0_node c3_node)) ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node)))
  have n0 : ((shared_expr_Repair195_30 c0_node c0_sign c3_node) ↔ ((shared_expr_Repair195_27 c0_node c0_sign c3_node) ∨ (shared_expr_Repair195_28 c0_node c3_node))) := by
    exact Iff.mp (normalization_9035 c0_node c0_sign c3_node) (replay_15416 c0_node c0_sign c3_node)
  have n1 : (((shared_expr_Repair195_27 c0_node c0_sign c3_node) ∨ (shared_expr_Repair195_28 c0_node c3_node)) ↔ ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node))) := by
    exact Iff.mp (normalization_9037 c0_node c0_sign c3_node) (replay_15417 c0_node c0_sign c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9038 c0_node c0_sign c3_node) hn

theorem normalized_2950 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9039 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_9040 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_9041 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (and_congr (normalization_9039 c0_depth c3_depth) (normalization_9040 c0_depth c3_depth))

abbrev shared_expr_Repair195_32 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
theorem normalization_9042 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Repair195_32 c0_depth c3_depth) := (iff_congr (normalization_8944 c0_depth c3_depth) (normalization_9041 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_15419 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2950 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_9042 c0_depth c3_depth) hn

abbrev shared_expr_Repair195_33 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))
abbrev formula_3625 (c0_depth c3_depth : Int) : Prop := (shared_expr_Repair195_33 c0_depth c3_depth)

theorem normalized_2951 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9043 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := (not_congr (normalization_9039 c0_depth c3_depth))

theorem normalization_9044 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (not_congr (normalization_9040 c0_depth c3_depth))

theorem normalization_9045 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) := (or_congr (normalization_9043 c0_depth c3_depth) (normalization_9044 c0_depth c3_depth))

theorem normalization_9046 (c0_depth c3_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))) := (not_congr (normalization_9045 c0_depth c3_depth))

abbrev shared_expr_Repair195_34 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))))
theorem normalization_9047 (c0_depth c3_depth : Int) : (formula_3625 c0_depth c3_depth) ↔ (shared_expr_Repair195_34 c0_depth c3_depth) := (iff_congr (normalization_9041 c0_depth c3_depth) (normalization_9046 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_15420 (c0_depth c3_depth : Int) : (formula_3625 c0_depth c3_depth) := by
  classical
  have ht := (normalized_2951 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9047 c0_depth c3_depth) hn

theorem normalized_2952 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9048 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Repair195_34 c0_depth c3_depth) := (iff_congr (normalization_8944 c0_depth c3_depth) (normalization_9046 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_15421 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2952 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (shared_expr_Repair195_34 c0_depth c3_depth))
  have n0 : (shared_expr_Repair195_32 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9042 c0_depth c3_depth) (replay_15419 c0_depth c3_depth)
  have n1 : (shared_expr_Repair195_34 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9047 c0_depth c3_depth) (replay_15420 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9048 c0_depth c3_depth) hn

theorem normalized_2953 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9049 (c0_depth c3_depth : Int) : (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))) := (not_congr (normalization_9046 c0_depth c3_depth))

abbrev shared_expr_Repair195_35 (c0_depth c3_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))))
theorem normalization_9050 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))) ↔ (shared_expr_Repair195_35 c0_depth c3_depth) := (iff_congr (normalization_8945 c0_depth c3_depth) (normalization_9049 c0_depth c3_depth))

-- Checked replay of monotonicity.
theorem replay_15422 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_2953 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair195_34 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9048 c0_depth c3_depth) (replay_15421 c0_depth c3_depth)
  have hn := ht n0
  exact Iff.mpr (normalization_9050 c0_depth c3_depth) hn

abbrev shared_expr_Repair195_36 (c0_depth c3_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))
abbrev formula_3626 (c0_depth c3_depth : Int) : Prop := (shared_expr_Repair195_36 c0_depth c3_depth)

theorem normalized_2954 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_37 (c0_depth c3_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
theorem normalization_9051 (c0_depth c3_depth : Int) : (formula_3626 c0_depth c3_depth) ↔ (shared_expr_Repair195_37 c0_depth c3_depth) := (iff_congr (normalization_9049 c0_depth c3_depth) (normalization_9045 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_15423 (c0_depth c3_depth : Int) : (formula_3626 c0_depth c3_depth) := by
  classical
  have ht := (normalized_2954 ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_9051 c0_depth c3_depth) hn

theorem normalized_2955 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_38 (c0_depth c3_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
theorem normalization_9052 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (shared_expr_Repair195_38 c0_depth c3_depth) := (iff_congr (normalization_8945 c0_depth c3_depth) (normalization_9045 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_15424 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) := by
  classical
  have ht := (normalized_2955 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair195_35 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9050 c0_depth c3_depth) (replay_15422 c0_depth c3_depth)
  have n1 : (shared_expr_Repair195_37 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9051 c0_depth c3_depth) (replay_15423 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9052 c0_depth c3_depth) hn

theorem normalized_2956 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9053 (c0_node c3_node : Int) : ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_9054 (c0_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (and_congr (normalization_8947 c0_node c3_node) (normalization_9053 c0_node c3_node))

abbrev shared_expr_Repair195_39 (c0_node c3_node : Int) : Prop := (((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
theorem normalization_9055 (c0_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Repair195_39 c0_node c3_node) := (iff_congr (normalization_8946 c0_node c3_node) (normalization_9054 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_15425 (c0_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2956 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_9055 c0_node c3_node) hn

abbrev shared_expr_Repair195_40 (c0_node c3_node : Int) : Prop := ((((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_3627 (c0_node c3_node : Int) : Prop := (shared_expr_Repair195_40 c0_node c3_node)

theorem normalized_2957 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9056 (c0_node c3_node : Int) : (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_9053 c0_node c3_node))

theorem normalization_9057 (c0_node c3_node : Int) : ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) := (or_congr (normalization_8948 c0_node c3_node) (normalization_9056 c0_node c3_node))

theorem normalization_9058 (c0_node c3_node : Int) : (¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) := (not_congr (normalization_9057 c0_node c3_node))

abbrev shared_expr_Repair195_41 (c0_node c3_node : Int) : Prop := (((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))))
theorem normalization_9059 (c0_node c3_node : Int) : (formula_3627 c0_node c3_node) ↔ (shared_expr_Repair195_41 c0_node c3_node) := (iff_congr (normalization_9054 c0_node c3_node) (normalization_9058 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_15426 (c0_node c3_node : Int) : (formula_3627 c0_node c3_node) := by
  classical
  have ht := (normalized_2957 (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9059 c0_node c3_node) hn

abbrev shared_expr_Repair195_42 (c0_node c3_node : Int) : Prop := (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_3628 (c0_node c3_node : Int) : Prop := (shared_expr_Repair195_42 c0_node c3_node)

theorem normalized_2958 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9060 (c0_node c3_node : Int) : (formula_3628 c0_node c3_node) ↔ (shared_expr_Repair195_41 c0_node c3_node) := (iff_congr (normalization_8946 c0_node c3_node) (normalization_9058 c0_node c3_node))

-- Checked replay of trans.
theorem replay_15427 (c0_node c3_node : Int) : (formula_3628 c0_node c3_node) := by
  classical
  have ht := (normalized_2958 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) (shared_expr_Repair195_41 c0_node c3_node))
  have n0 : (shared_expr_Repair195_39 c0_node c3_node) := by
    exact Iff.mp (normalization_9055 c0_node c3_node) (replay_15425 c0_node c3_node)
  have n1 : (shared_expr_Repair195_41 c0_node c3_node) := by
    exact Iff.mp (normalization_9059 c0_node c3_node) (replay_15426 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9060 c0_node c3_node) hn

abbrev shared_expr_Repair195_43 (c0_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair195_44 (c0_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_3629 (c0_node c3_node c3_sign : Int) : Prop := ((shared_expr_Repair195_43 c0_node c3_node c3_sign) ∨ (shared_expr_Repair195_44 c0_node c3_node))

theorem normalized_2959 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_45 (c0_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair195_46 (c0_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_9061 (c0_node c3_node c3_sign : Int) : (formula_3629 c0_node c3_node c3_sign) ↔ ((shared_expr_Repair195_45 c0_node c3_node c3_sign) ∨ (shared_expr_Repair195_46 c0_node c3_node)) := (or_congr (and_congr (normalization_9058 c0_node c3_node) (normalization_6992 c3_sign)) (and_congr (not_congr (normalization_9058 c0_node c3_node)) (normalization_8948 c0_node c3_node)))

abbrev shared_expr_Repair195_47 (c0_node c3_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair195_48 (c0_node c3_node c3_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair195_47 c0_node c3_node))
theorem normalization_9062 (c0_node c3_node c3_sign : Int) : ((formula_3607 c0_node c3_node c3_sign) ↔ (formula_3629 c0_node c3_node c3_sign)) ↔ ((shared_expr_Repair195_48 c0_node c3_node c3_sign) ↔ ((shared_expr_Repair195_45 c0_node c3_node c3_sign) ∨ (shared_expr_Repair195_46 c0_node c3_node))) := (iff_congr (normalization_8949 c0_node c3_node c3_sign) (normalization_9061 c0_node c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_15428 (c0_node c3_node c3_sign : Int) : ((formula_3607 c0_node c3_node c3_sign) ↔ (formula_3629 c0_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2959 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair195_41 c0_node c3_node) := by
    exact Iff.mp (normalization_9060 c0_node c3_node) (replay_15427 c0_node c3_node)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6994 c3_sign) (replay_6142 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9062 c0_node c3_node c3_sign) hn

theorem normalized_2960 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_49 (c0_node c3_node : Int) : Prop := (((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_9063 (c0_node c3_node c3_sign : Int) : (formula_3578 c0_node c3_node c3_sign) ↔ ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign)) := (or_congr (and_congr (normalization_9057 c0_node c3_node) (normalization_8948 c0_node c3_node)) (and_congr (not_congr (normalization_9057 c0_node c3_node)) (normalization_6992 c3_sign)))

theorem normalization_9064 (c0_node c3_node c3_sign : Int) : ((formula_3629 c0_node c3_node c3_sign) ↔ (formula_3578 c0_node c3_node c3_sign)) ↔ (((shared_expr_Repair195_45 c0_node c3_node c3_sign) ∨ (shared_expr_Repair195_46 c0_node c3_node)) ↔ ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign))) := (iff_congr (normalization_9061 c0_node c3_node c3_sign) (normalization_9063 c0_node c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_15429 (c0_node c3_node c3_sign : Int) : ((formula_3629 c0_node c3_node c3_sign) ↔ (formula_3578 c0_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2960 ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9064 c0_node c3_node c3_sign) hn

theorem normalized_2961 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9065 (c0_node c3_node c3_sign : Int) : ((formula_3607 c0_node c3_node c3_sign) ↔ (formula_3578 c0_node c3_node c3_sign)) ↔ ((shared_expr_Repair195_48 c0_node c3_node c3_sign) ↔ ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign))) := (iff_congr (normalization_8949 c0_node c3_node c3_sign) (normalization_9063 c0_node c3_node c3_sign))

-- Checked replay of trans.
theorem replay_15430 (c0_node c3_node c3_sign : Int) : ((formula_3607 c0_node c3_node c3_sign) ↔ (formula_3578 c0_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2961 (shared_expr_Repair195_48 c0_node c3_node c3_sign) ((shared_expr_Repair195_45 c0_node c3_node c3_sign) ∨ (shared_expr_Repair195_46 c0_node c3_node)) ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign)))
  have n0 : ((shared_expr_Repair195_48 c0_node c3_node c3_sign) ↔ ((shared_expr_Repair195_45 c0_node c3_node c3_sign) ∨ (shared_expr_Repair195_46 c0_node c3_node))) := by
    exact Iff.mp (normalization_9062 c0_node c3_node c3_sign) (replay_15428 c0_node c3_node c3_sign)
  have n1 : (((shared_expr_Repair195_45 c0_node c3_node c3_sign) ∨ (shared_expr_Repair195_46 c0_node c3_node)) ↔ ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign))) := by
    exact Iff.mp (normalization_9064 c0_node c3_node c3_sign) (replay_15429 c0_node c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9065 c0_node c3_node c3_sign) hn

abbrev shared_expr_Repair195_50 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_3607 c0_node c3_node c3_sign)) ↔ (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_3578 c0_node c3_node c3_sign)))
abbrev formula_3630 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_50 c0_depth c0_node c3_depth c3_node c3_sign)

theorem normalized_2962 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_51 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign)))
theorem normalization_9066 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_3578 c0_node c3_node c3_sign)) ↔ (shared_expr_Repair195_51 c0_depth c0_node c3_depth c3_node c3_sign) := (or_congr (normalization_9045 c0_depth c3_depth) (normalization_9063 c0_node c3_node c3_sign))

abbrev shared_expr_Repair195_52 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair195_48 c0_node c3_node c3_sign)) ↔ (shared_expr_Repair195_51 c0_depth c0_node c3_depth c3_node c3_sign))
theorem normalization_9067 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (formula_3630 c0_depth c0_node c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_52 c0_depth c0_node c3_depth c3_node c3_sign) := (iff_congr (normalization_8950 c0_depth c0_node c3_depth c3_node c3_sign) (normalization_9066 c0_depth c0_node c3_depth c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_15431 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (formula_3630 c0_depth c0_node c3_depth c3_node c3_sign) := by
  classical
  have ht := (normalized_2962 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) (shared_expr_Repair195_48 c0_node c3_node c3_sign) ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign)))
  have n0 : (shared_expr_Repair195_38 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9052 c0_depth c3_depth) (replay_15424 c0_depth c3_depth)
  have n1 : ((shared_expr_Repair195_48 c0_node c3_node c3_sign) ↔ ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign))) := by
    exact Iff.mp (normalization_9065 c0_node c3_node c3_sign) (replay_15430 c0_node c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9067 c0_depth c0_node c3_depth c3_node c3_sign) hn

abbrev shared_expr_Repair195_53 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_3578 c0_node c3_node c3_sign)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_3578 c0_node c3_node c3_sign)))
abbrev formula_3631 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_53 c0_depth c0_node c3_depth c3_node c3_sign)

theorem normalized_2963 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_54 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ∨ ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign)))
theorem normalization_9068 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_3578 c0_node c3_node c3_sign)) ↔ (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign) := (or_congr (normalization_9043 c0_depth c3_depth) (or_congr (normalization_9044 c0_depth c3_depth) (normalization_9063 c0_node c3_node c3_sign)))

theorem normalization_9069 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (formula_3631 c0_depth c0_node c3_depth c3_node c3_sign) ↔ ((shared_expr_Repair195_51 c0_depth c0_node c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign)) := (iff_congr (normalization_9066 c0_depth c0_node c3_depth c3_node c3_sign) (normalization_9068 c0_depth c0_node c3_depth c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_15432 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (formula_3631 c0_depth c0_node c3_depth c3_node c3_sign) := by
  classical
  have ht := (normalized_2963 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((shared_expr_Repair195_49 c0_node c3_node) ∨ (shared_expr_Repair195_45 c0_node c3_node c3_sign)))
  have hn := ht
  exact Iff.mpr (normalization_9069 c0_depth c0_node c3_depth c3_node c3_sign) hn

abbrev shared_expr_Repair195_55 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_3607 c0_node c3_node c3_sign)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_3578 c0_node c3_node c3_sign)))
abbrev formula_3632 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_55 c0_depth c0_node c3_depth c3_node c3_sign)

theorem normalized_2964 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_56 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair195_48 c0_node c3_node c3_sign)) ↔ (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign))
theorem normalization_9070 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (formula_3632 c0_depth c0_node c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_56 c0_depth c0_node c3_depth c3_node c3_sign) := (iff_congr (normalization_8950 c0_depth c0_node c3_depth c3_node c3_sign) (normalization_9068 c0_depth c0_node c3_depth c3_node c3_sign))

-- Checked replay of trans.
theorem replay_15433 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (formula_3632 c0_depth c0_node c3_depth c3_node c3_sign) := by
  classical
  have ht := (normalized_2964 ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair195_48 c0_node c3_node c3_sign)) (shared_expr_Repair195_51 c0_depth c0_node c3_depth c3_node c3_sign) (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign))
  have n0 : (shared_expr_Repair195_52 c0_depth c0_node c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_9067 c0_depth c0_node c3_depth c3_node c3_sign) (replay_15431 c0_depth c0_node c3_depth c3_node c3_sign)
  have n1 : ((shared_expr_Repair195_51 c0_depth c0_node c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_9069 c0_depth c0_node c3_depth c3_node c3_sign) (replay_15432 c0_depth c0_node c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9070 c0_depth c0_node c3_depth c3_node c3_sign) hn

abbrev shared_expr_Repair195_57 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_3578 c0_node c3_node c3_sign)))
abbrev shared_expr_Repair195_58 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ∧ (formula_3579 c0_node c0_sign c3_node)) ∨ (shared_expr_Repair195_57 c0_depth c0_node c3_depth c3_node c3_sign))
abbrev formula_3633 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_58 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)

theorem normalized_2965 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_59 (c0_depth c0_node c0_sign c3_depth c3_node : Int) : Prop := ((¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))) ∧ ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node)))
abbrev shared_expr_Repair195_60 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))))) ∧ (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign))
theorem normalization_9071 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : (formula_3633 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ ((shared_expr_Repair195_59 c0_depth c0_node c0_sign c3_depth c3_node) ∨ (shared_expr_Repair195_60 c0_depth c0_node c3_depth c3_node c3_sign)) := (or_congr (and_congr (normalization_9023 c0_depth c3_depth) (normalization_9036 c0_node c0_sign c3_node)) (and_congr (not_congr (normalization_9023 c0_depth c3_depth)) (normalization_9068 c0_depth c0_node c3_depth c3_node c3_sign)))

abbrev shared_expr_Repair195_61 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair195_48 c0_node c3_node c3_sign)))
abbrev shared_expr_Repair195_62 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair195_30 c0_node c0_sign c3_node)) ∨ (shared_expr_Repair195_61 c0_depth c0_node c3_depth c3_node c3_sign))
abbrev shared_expr_Repair195_63 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := ((shared_expr_Repair195_62 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ ((shared_expr_Repair195_59 c0_depth c0_node c0_sign c3_depth c3_node) ∨ (shared_expr_Repair195_60 c0_depth c0_node c3_depth c3_node c3_sign)))
theorem normalization_9072 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3608 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3633 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (shared_expr_Repair195_63 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) := (iff_congr (normalization_8951 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (normalization_9071 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_15434 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3608 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3633 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_2965 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) (shared_expr_Repair195_30 c0_node c0_sign c3_node) ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node)) ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair195_48 c0_node c3_node c3_sign)) (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign))
  have n0 : (shared_expr_Repair195_20 c0_depth c3_depth) := by
    exact Iff.mp (normalization_9025 c0_depth c3_depth) (replay_15412 c0_depth c3_depth)
  have n1 : ((shared_expr_Repair195_30 c0_node c0_sign c3_node) ↔ ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node))) := by
    exact Iff.mp (normalization_9038 c0_node c0_sign c3_node) (replay_15418 c0_node c0_sign c3_node)
  have n2 : (shared_expr_Repair195_56 c0_depth c0_node c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_9070 c0_depth c0_node c3_depth c3_node c3_sign) (replay_15433 c0_depth c0_node c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_9072 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) hn

theorem normalized_2966 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_64 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign)) ∨ (shared_expr_Repair195_59 c0_depth c0_node c0_sign c3_depth c3_node))
theorem normalization_9073 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : (formula_3580 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_9022 c0_depth c3_depth) (normalization_9068 c0_depth c0_node c3_depth c3_node c3_sign)) (and_congr (not_congr (normalization_9022 c0_depth c3_depth)) (normalization_9036 c0_node c0_sign c3_node)))

abbrev shared_expr_Repair195_65 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := (((shared_expr_Repair195_59 c0_depth c0_node c0_sign c3_depth c3_node) ∨ (shared_expr_Repair195_60 c0_depth c0_node c3_depth c3_node c3_sign)) ↔ (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
theorem normalization_9074 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3633 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3580 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (shared_expr_Repair195_65 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) := (iff_congr (normalization_9071 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (normalization_9073 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_15435 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3633 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3580 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_2966 ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ((shared_expr_Repair195_31 c0_node c3_node) ∨ (shared_expr_Repair195_27 c0_node c0_sign c3_node)) (shared_expr_Repair195_54 c0_depth c0_node c3_depth c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_9074 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) hn

theorem normalized_2967 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9075 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3608 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3580 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ ((shared_expr_Repair195_62 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := (iff_congr (normalization_8951 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (normalization_9073 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

-- Checked replay of trans.
theorem replay_15436 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3608 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3580 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_2967 (shared_expr_Repair195_62 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ((shared_expr_Repair195_59 c0_depth c0_node c0_sign c3_depth c3_node) ∨ (shared_expr_Repair195_60 c0_depth c0_node c3_depth c3_node c3_sign)) (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
  have n0 : (shared_expr_Repair195_63 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_9072 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (replay_15434 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)
  have n1 : (shared_expr_Repair195_65 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_9074 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (replay_15435 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9075 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) hn

abbrev shared_expr_Repair195_66 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ∧ (formula_3581 c0_node c0_sign c3_node c3_sign)) ∨ ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ∧ (formula_3580 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))
abbrev formula_3634 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_66 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)

theorem normalized_2968 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_67 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
abbrev shared_expr_Repair195_68 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign)) ∨ (shared_expr_Repair195_67 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
theorem normalization_9076 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : (formula_3634 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_68 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_8986 c0_depth c3_depth) (normalization_9013 c0_node c0_sign c3_node c3_sign)) (and_congr (not_congr (normalization_8986 c0_depth c3_depth)) (normalization_9073 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))

abbrev shared_expr_Repair195_69 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair195_15 c0_node c0_sign c3_node c3_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair195_62 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))
theorem normalization_9077 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3609 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3634 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ ((shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_68 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := (iff_congr (normalization_8952 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (normalization_9076 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_15437 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3609 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3634 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_2968 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) (shared_expr_Repair195_15 c0_node c0_sign c3_node c3_sign) (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign) (shared_expr_Repair195_62 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
  have n0 : (shared_expr_Repair195_0 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8989 c0_depth c3_depth) (replay_15396 c0_depth c3_depth)
  have n1 : ((shared_expr_Repair195_15 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_9015 c0_node c0_sign c3_node c3_sign) (replay_15409 c0_node c0_sign c3_node c3_sign)
  have n2 : ((shared_expr_Repair195_62 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_9075 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (replay_15436 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_9077 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) hn

theorem normalized_2969 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_70 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign)))
theorem normalization_9078 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_8985 c0_depth c3_depth) (normalization_9073 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) (and_congr (not_congr (normalization_8985 c0_depth c3_depth)) (normalization_9013 c0_node c0_sign c3_node c3_sign)))

theorem normalization_9079 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3634 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ ((shared_expr_Repair195_68 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := (iff_congr (normalization_9076 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (normalization_9078 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_15438 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3634 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_2969 ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) (shared_expr_Repair195_16 c0_node c0_sign c3_node c3_sign) (shared_expr_Repair195_64 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_9079 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) hn

theorem normalized_2970 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9080 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3609 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ ((shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := (iff_congr (normalization_8952 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (normalization_9078 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

-- Checked replay of trans.
theorem replay_15439 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : ((formula_3609 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_2970 (shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (shared_expr_Repair195_68 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
  have n0 : ((shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_68 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_9077 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (replay_15437 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)
  have n1 : ((shared_expr_Repair195_68 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_9079 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (replay_15438 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9080 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) hn

abbrev shared_expr_Repair195_71 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (c3_kind = (2 : Int))) ∧ (formula_3609 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) ∧ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))
abbrev formula_3635 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_71 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_2971 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∧ p2) ↔ (p1 ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9081 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : (((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) ∧ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := (and_congr (normalization_6941 c3_kind) (normalization_9078 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

abbrev shared_expr_Repair195_72 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))
theorem normalization_9082 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_3635 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Repair195_72 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_8953 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) (normalization_9081 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_15440 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_3635 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_2971 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) (shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
  have n0 : ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_6948 c3_kind) (replay_6122 c3_kind)
  have n1 : ((shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_9080 c0_depth c0_node c0_sign c3_depth c3_node c3_sign) (replay_15439 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9082 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Repair195_73 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) ∧ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))))
abbrev formula_3636 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_73 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_2972 (p0 p1 : Prop) : ((p0 ∧ p1) ↔ (¬ ((¬ p0) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9083 (c0_depth c0_node c0_sign c3_depth c3_node c3_sign : Int) : (¬ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (¬ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) := (not_congr (normalization_9078 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

theorem normalization_9084 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))) ↔ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))) := (or_congr (normalization_6942 c3_kind) (normalization_9083 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))

theorem normalization_9085 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))) := (not_congr (normalization_9084 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign))

abbrev shared_expr_Repair195_74 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))))
theorem normalization_9086 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_3636 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Repair195_74 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_9081 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) (normalization_9085 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_15441 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_3636 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_2972 ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_9086 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Repair195_75 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (c3_kind = (2 : Int))) ∧ (formula_3609 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_3582 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))))
abbrev formula_3637 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Repair195_75 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_2973 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair195_76 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)))))
theorem normalization_9087 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_3637 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Repair195_76 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_8953 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) (normalization_9085 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of trans.
theorem replay_15442 (c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_3637 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_2973 ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair195_69 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) (((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign)) ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair195_70 c0_depth c0_node c0_sign c3_depth c3_node c3_sign))))
  have n0 : (shared_expr_Repair195_72 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_9082 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) (replay_15440 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign)
  have n1 : (shared_expr_Repair195_74 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_9086 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) (replay_15441 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9087 c0_depth c0_node c0_sign c3_depth c3_kind c3_node c3_sign) hn

end H4Formal.Generated.Repair
