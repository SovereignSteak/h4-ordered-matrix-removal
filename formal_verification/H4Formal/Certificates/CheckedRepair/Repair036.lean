import H4Formal.Certificates.CheckedRepair.Repair035

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_795 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_0 (c0_node c2_node : Int) : Prop := (((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair036_1 (c0_node c0_sign c2_node : Int) : Prop := ((¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))))
theorem normalization_3153 (c0_node c0_sign c2_node : Int) : (formula_792 c0_node c0_sign c2_node) ↔ ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node)) := (or_congr (and_congr (normalization_3147 c0_node c2_node) (normalization_3029 c0_node c2_node)) (and_congr (not_congr (normalization_3147 c0_node c2_node)) (normalization_461 c0_sign)))

abbrev shared_expr_Repair036_2 (c0_node c2_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3154 (c0_node c0_sign c2_node : Int) : ((formula_833 c0_node c0_sign c2_node) ↔ (formula_792 c0_node c0_sign c2_node)) ↔ (((shared_expr_Repair036_1 c0_node c0_sign c2_node) ∨ (shared_expr_Repair036_2 c0_node c2_node)) ↔ ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node))) := (iff_congr (normalization_3151 c0_node c0_sign c2_node) (normalization_3153 c0_node c0_sign c2_node))

-- Checked replay of rewrite.
theorem replay_2194 (c0_node c0_sign c2_node : Int) : ((formula_833 c0_node c0_sign c2_node) ↔ (formula_792 c0_node c0_sign c2_node)) := by
  classical
  have ht := (normalized_795 ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3154 c0_node c0_sign c2_node) hn

theorem normalized_796 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_3 (c0_node c2_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair036_4 (c0_node c0_sign c2_node : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair036_3 c0_node c2_node))
theorem normalization_3155 (c0_node c0_sign c2_node : Int) : ((formula_815 c0_node c0_sign c2_node) ↔ (formula_792 c0_node c0_sign c2_node)) ↔ ((shared_expr_Repair036_4 c0_node c0_sign c2_node) ↔ ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node))) := (iff_congr (normalization_3030 c0_node c0_sign c2_node) (normalization_3153 c0_node c0_sign c2_node))

-- Checked replay of trans.
theorem replay_2195 (c0_node c0_sign c2_node : Int) : ((formula_815 c0_node c0_sign c2_node) ↔ (formula_792 c0_node c0_sign c2_node)) := by
  classical
  have ht := (normalized_796 (shared_expr_Repair036_4 c0_node c0_sign c2_node) ((shared_expr_Repair036_1 c0_node c0_sign c2_node) ∨ (shared_expr_Repair036_2 c0_node c2_node)) ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node)))
  have n0 : ((shared_expr_Repair036_4 c0_node c0_sign c2_node) ↔ ((shared_expr_Repair036_1 c0_node c0_sign c2_node) ∨ (shared_expr_Repair036_2 c0_node c2_node))) := by
    exact Iff.mp (normalization_3152 c0_node c0_sign c2_node) (replay_2193 c0_node c0_sign c2_node)
  have n1 : (((shared_expr_Repair036_1 c0_node c0_sign c2_node) ∨ (shared_expr_Repair036_2 c0_node c2_node)) ↔ ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node))) := by
    exact Iff.mp (normalization_3154 c0_node c0_sign c2_node) (replay_2194 c0_node c0_sign c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3155 c0_node c0_sign c2_node) hn

theorem normalized_797 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3156 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_3157 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_3158 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := (and_congr (normalization_3156 c0_depth c2_depth) (normalization_3157 c0_depth c2_depth))

abbrev shared_expr_Repair036_5 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))
theorem normalization_3159 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Repair036_5 c0_depth c2_depth) := (iff_congr (normalization_3031 c0_depth c2_depth) (normalization_3158 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2196 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_797 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3159 c0_depth c2_depth) hn

abbrev shared_expr_Repair036_6 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))
abbrev formula_834 (c0_depth c2_depth : Int) : Prop := (shared_expr_Repair036_6 c0_depth c2_depth)

theorem normalized_798 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3160 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) := (not_congr (normalization_3156 c0_depth c2_depth))

theorem normalization_3161 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := (not_congr (normalization_3157 c0_depth c2_depth))

theorem normalization_3162 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) := (or_congr (normalization_3160 c0_depth c2_depth) (normalization_3161 c0_depth c2_depth))

theorem normalization_3163 (c0_depth c2_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) := (not_congr (normalization_3162 c0_depth c2_depth))

abbrev shared_expr_Repair036_7 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))))
theorem normalization_3164 (c0_depth c2_depth : Int) : (formula_834 c0_depth c2_depth) ↔ (shared_expr_Repair036_7 c0_depth c2_depth) := (iff_congr (normalization_3158 c0_depth c2_depth) (normalization_3163 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2197 (c0_depth c2_depth : Int) : (formula_834 c0_depth c2_depth) := by
  classical
  have ht := (normalized_798 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3164 c0_depth c2_depth) hn

theorem normalized_799 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3165 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Repair036_7 c0_depth c2_depth) := (iff_congr (normalization_3031 c0_depth c2_depth) (normalization_3163 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_2198 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_799 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) (shared_expr_Repair036_7 c0_depth c2_depth))
  have n0 : (shared_expr_Repair036_5 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3159 c0_depth c2_depth) (replay_2196 c0_depth c2_depth)
  have n1 : (shared_expr_Repair036_7 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3164 c0_depth c2_depth) (replay_2197 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3165 c0_depth c2_depth) hn

theorem normalized_800 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3166 (c0_depth c2_depth : Int) : (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))) := (not_congr (normalization_3163 c0_depth c2_depth))

abbrev shared_expr_Repair036_8 (c0_depth c2_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))))
theorem normalization_3167 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))) ↔ (shared_expr_Repair036_8 c0_depth c2_depth) := (iff_congr (normalization_3032 c0_depth c2_depth) (normalization_3166 c0_depth c2_depth))

-- Checked replay of monotonicity.
theorem replay_2199 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_800 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair036_7 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3165 c0_depth c2_depth) (replay_2198 c0_depth c2_depth)
  have hn := ht n0
  exact Iff.mpr (normalization_3167 c0_depth c2_depth) hn

abbrev shared_expr_Repair036_9 (c0_depth c2_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))
abbrev formula_835 (c0_depth c2_depth : Int) : Prop := (shared_expr_Repair036_9 c0_depth c2_depth)

theorem normalized_801 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_10 (c0_depth c2_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
theorem normalization_3168 (c0_depth c2_depth : Int) : (formula_835 c0_depth c2_depth) ↔ (shared_expr_Repair036_10 c0_depth c2_depth) := (iff_congr (normalization_3166 c0_depth c2_depth) (normalization_3162 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2200 (c0_depth c2_depth : Int) : (formula_835 c0_depth c2_depth) := by
  classical
  have ht := (normalized_801 ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_3168 c0_depth c2_depth) hn

theorem normalized_802 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_11 (c0_depth c2_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
theorem normalization_3169 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (shared_expr_Repair036_11 c0_depth c2_depth) := (iff_congr (normalization_3032 c0_depth c2_depth) (normalization_3162 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_2201 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) := by
  classical
  have ht := (normalized_802 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair036_8 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3167 c0_depth c2_depth) (replay_2199 c0_depth c2_depth)
  have n1 : (shared_expr_Repair036_10 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3168 c0_depth c2_depth) (replay_2200 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3169 c0_depth c2_depth) hn

theorem normalized_803 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3170 (c0_node c2_node : Int) : ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3171 (c0_node c2_node : Int) : (((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (and_congr (normalization_3034 c0_node c2_node) (normalization_3170 c0_node c2_node))

abbrev shared_expr_Repair036_12 (c0_node c2_node : Int) : Prop := (((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_3172 (c0_node c2_node : Int) : (((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Repair036_12 c0_node c2_node) := (iff_congr (normalization_3033 c0_node c2_node) (normalization_3171 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_2202 (c0_node c2_node : Int) : (((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_803 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3172 c0_node c2_node) hn

abbrev shared_expr_Repair036_13 (c0_node c2_node : Int) : Prop := ((((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_836 (c0_node c2_node : Int) : Prop := (shared_expr_Repair036_13 c0_node c2_node)

theorem normalized_804 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3173 (c0_node c2_node : Int) : (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_3170 c0_node c2_node))

theorem normalization_3174 (c0_node c2_node : Int) : ((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) := (or_congr (normalization_3035 c0_node c2_node) (normalization_3173 c0_node c2_node))

theorem normalization_3175 (c0_node c2_node : Int) : (¬ ((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) := (not_congr (normalization_3174 c0_node c2_node))

abbrev shared_expr_Repair036_14 (c0_node c2_node : Int) : Prop := (((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
theorem normalization_3176 (c0_node c2_node : Int) : (formula_836 c0_node c2_node) ↔ (shared_expr_Repair036_14 c0_node c2_node) := (iff_congr (normalization_3171 c0_node c2_node) (normalization_3175 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_2203 (c0_node c2_node : Int) : (formula_836 c0_node c2_node) := by
  classical
  have ht := (normalized_804 (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3176 c0_node c2_node) hn

abbrev shared_expr_Repair036_15 (c0_node c2_node : Int) : Prop := (((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_837 (c0_node c2_node : Int) : Prop := (shared_expr_Repair036_15 c0_node c2_node)

theorem normalized_805 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3177 (c0_node c2_node : Int) : (formula_837 c0_node c2_node) ↔ (shared_expr_Repair036_14 c0_node c2_node) := (iff_congr (normalization_3033 c0_node c2_node) (normalization_3175 c0_node c2_node))

-- Checked replay of trans.
theorem replay_2204 (c0_node c2_node : Int) : (formula_837 c0_node c2_node) := by
  classical
  have ht := (normalized_805 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) (shared_expr_Repair036_14 c0_node c2_node))
  have n0 : (shared_expr_Repair036_12 c0_node c2_node) := by
    exact Iff.mp (normalization_3172 c0_node c2_node) (replay_2202 c0_node c2_node)
  have n1 : (shared_expr_Repair036_14 c0_node c2_node) := by
    exact Iff.mp (normalization_3176 c0_node c2_node) (replay_2203 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3177 c0_node c2_node) hn

abbrev shared_expr_Repair036_16 (c0_node c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair036_17 (c0_node c2_node : Int) : Prop := ((¬ (¬ ((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_838 (c0_node c2_node c2_sign : Int) : Prop := ((shared_expr_Repair036_16 c0_node c2_node c2_sign) ∨ (shared_expr_Repair036_17 c0_node c2_node))

theorem normalized_806 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_18 (c0_node c2_node c2_sign : Int) : Prop := ((¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair036_19 (c0_node c2_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_3178 (c0_node c2_node c2_sign : Int) : (formula_838 c0_node c2_node c2_sign) ↔ ((shared_expr_Repair036_18 c0_node c2_node c2_sign) ∨ (shared_expr_Repair036_19 c0_node c2_node)) := (or_congr (and_congr (normalization_3175 c0_node c2_node) (normalization_119 c2_sign)) (and_congr (not_congr (normalization_3175 c0_node c2_node)) (normalization_3035 c0_node c2_node)))

abbrev shared_expr_Repair036_20 (c0_node c2_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair036_21 (c0_node c2_node c2_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair036_20 c0_node c2_node))
theorem normalization_3179 (c0_node c2_node c2_sign : Int) : ((formula_816 c0_node c2_node c2_sign) ↔ (formula_838 c0_node c2_node c2_sign)) ↔ ((shared_expr_Repair036_21 c0_node c2_node c2_sign) ↔ ((shared_expr_Repair036_18 c0_node c2_node c2_sign) ∨ (shared_expr_Repair036_19 c0_node c2_node))) := (iff_congr (normalization_3036 c0_node c2_node c2_sign) (normalization_3178 c0_node c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2205 (c0_node c2_node c2_sign : Int) : ((formula_816 c0_node c2_node c2_sign) ↔ (formula_838 c0_node c2_node c2_sign)) := by
  classical
  have ht := (normalized_806 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair036_14 c0_node c2_node) := by
    exact Iff.mp (normalization_3177 c0_node c2_node) (replay_2204 c0_node c2_node)
  have n1 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3121 c2_sign) (replay_2180 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3179 c0_node c2_node c2_sign) hn

theorem normalized_807 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_22 (c0_node c2_node : Int) : Prop := (((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_3180 (c0_node c2_node c2_sign : Int) : (formula_791 c0_node c2_node c2_sign) ↔ ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign)) := (or_congr (and_congr (normalization_3174 c0_node c2_node) (normalization_3035 c0_node c2_node)) (and_congr (not_congr (normalization_3174 c0_node c2_node)) (normalization_119 c2_sign)))

theorem normalization_3181 (c0_node c2_node c2_sign : Int) : ((formula_838 c0_node c2_node c2_sign) ↔ (formula_791 c0_node c2_node c2_sign)) ↔ (((shared_expr_Repair036_18 c0_node c2_node c2_sign) ∨ (shared_expr_Repair036_19 c0_node c2_node)) ↔ ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign))) := (iff_congr (normalization_3178 c0_node c2_node c2_sign) (normalization_3180 c0_node c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2206 (c0_node c2_node c2_sign : Int) : ((formula_838 c0_node c2_node c2_sign) ↔ (formula_791 c0_node c2_node c2_sign)) := by
  classical
  have ht := (normalized_807 ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3181 c0_node c2_node c2_sign) hn

theorem normalized_808 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3182 (c0_node c2_node c2_sign : Int) : ((formula_816 c0_node c2_node c2_sign) ↔ (formula_791 c0_node c2_node c2_sign)) ↔ ((shared_expr_Repair036_21 c0_node c2_node c2_sign) ↔ ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign))) := (iff_congr (normalization_3036 c0_node c2_node c2_sign) (normalization_3180 c0_node c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2207 (c0_node c2_node c2_sign : Int) : ((formula_816 c0_node c2_node c2_sign) ↔ (formula_791 c0_node c2_node c2_sign)) := by
  classical
  have ht := (normalized_808 (shared_expr_Repair036_21 c0_node c2_node c2_sign) ((shared_expr_Repair036_18 c0_node c2_node c2_sign) ∨ (shared_expr_Repair036_19 c0_node c2_node)) ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign)))
  have n0 : ((shared_expr_Repair036_21 c0_node c2_node c2_sign) ↔ ((shared_expr_Repair036_18 c0_node c2_node c2_sign) ∨ (shared_expr_Repair036_19 c0_node c2_node))) := by
    exact Iff.mp (normalization_3179 c0_node c2_node c2_sign) (replay_2205 c0_node c2_node c2_sign)
  have n1 : (((shared_expr_Repair036_18 c0_node c2_node c2_sign) ∨ (shared_expr_Repair036_19 c0_node c2_node)) ↔ ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign))) := by
    exact Iff.mp (normalization_3181 c0_node c2_node c2_sign) (replay_2206 c0_node c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3182 c0_node c2_node c2_sign) hn

abbrev shared_expr_Repair036_23 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ∨ (formula_816 c0_node c2_node c2_sign)) ↔ (((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ∨ (formula_791 c0_node c2_node c2_sign)))
abbrev formula_839 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_23 c0_depth c0_node c2_depth c2_node c2_sign)

theorem normalized_809 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_24 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign)))
theorem normalization_3183 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : (((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ∨ (formula_791 c0_node c2_node c2_sign)) ↔ (shared_expr_Repair036_24 c0_depth c0_node c2_depth c2_node c2_sign) := (or_congr (normalization_3162 c0_depth c2_depth) (normalization_3180 c0_node c2_node c2_sign))

abbrev shared_expr_Repair036_25 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair036_21 c0_node c2_node c2_sign)) ↔ (shared_expr_Repair036_24 c0_depth c0_node c2_depth c2_node c2_sign))
theorem normalization_3184 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : (formula_839 c0_depth c0_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_25 c0_depth c0_node c2_depth c2_node c2_sign) := (iff_congr (normalization_3037 c0_depth c0_node c2_depth c2_node c2_sign) (normalization_3183 c0_depth c0_node c2_depth c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2208 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : (formula_839 c0_depth c0_node c2_depth c2_node c2_sign) := by
  classical
  have ht := (normalized_809 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) (shared_expr_Repair036_21 c0_node c2_node c2_sign) ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign)))
  have n0 : (shared_expr_Repair036_11 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3169 c0_depth c2_depth) (replay_2201 c0_depth c2_depth)
  have n1 : ((shared_expr_Repair036_21 c0_node c2_node c2_sign) ↔ ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign))) := by
    exact Iff.mp (normalization_3182 c0_node c2_node c2_sign) (replay_2207 c0_node c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3184 c0_depth c0_node c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair036_26 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ∨ (formula_791 c0_node c2_node c2_sign)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_791 c0_node c2_node c2_sign)))
abbrev formula_840 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_26 c0_depth c0_node c2_depth c2_node c2_sign)

theorem normalized_810 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_27 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ∨ ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign)))
theorem normalization_3185 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_791 c0_node c2_node c2_sign)) ↔ (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign) := (or_congr (normalization_3160 c0_depth c2_depth) (or_congr (normalization_3161 c0_depth c2_depth) (normalization_3180 c0_node c2_node c2_sign)))

theorem normalization_3186 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : (formula_840 c0_depth c0_node c2_depth c2_node c2_sign) ↔ ((shared_expr_Repair036_24 c0_depth c0_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign)) := (iff_congr (normalization_3183 c0_depth c0_node c2_depth c2_node c2_sign) (normalization_3185 c0_depth c0_node c2_depth c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2209 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : (formula_840 c0_depth c0_node c2_depth c2_node c2_sign) := by
  classical
  have ht := (normalized_810 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((shared_expr_Repair036_22 c0_node c2_node) ∨ (shared_expr_Repair036_18 c0_node c2_node c2_sign)))
  have hn := ht
  exact Iff.mpr (normalization_3186 c0_depth c0_node c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair036_28 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ∨ (formula_816 c0_node c2_node c2_sign)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_791 c0_node c2_node c2_sign)))
abbrev formula_841 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_28 c0_depth c0_node c2_depth c2_node c2_sign)

theorem normalized_811 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_29 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair036_21 c0_node c2_node c2_sign)) ↔ (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign))
theorem normalization_3187 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : (formula_841 c0_depth c0_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_29 c0_depth c0_node c2_depth c2_node c2_sign) := (iff_congr (normalization_3037 c0_depth c0_node c2_depth c2_node c2_sign) (normalization_3185 c0_depth c0_node c2_depth c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2210 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : (formula_841 c0_depth c0_node c2_depth c2_node c2_sign) := by
  classical
  have ht := (normalized_811 ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair036_21 c0_node c2_node c2_sign)) (shared_expr_Repair036_24 c0_depth c0_node c2_depth c2_node c2_sign) (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign))
  have n0 : (shared_expr_Repair036_25 c0_depth c0_node c2_depth c2_node c2_sign) := by
    exact Iff.mp (normalization_3184 c0_depth c0_node c2_depth c2_node c2_sign) (replay_2208 c0_depth c0_node c2_depth c2_node c2_sign)
  have n1 : ((shared_expr_Repair036_24 c0_depth c0_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_3186 c0_depth c0_node c2_depth c2_node c2_sign) (replay_2209 c0_depth c0_node c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3187 c0_depth c0_node c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair036_30 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_791 c0_node c2_node c2_sign)))
abbrev shared_expr_Repair036_31 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))) ∧ (formula_792 c0_node c0_sign c2_node)) ∨ (shared_expr_Repair036_30 c0_depth c0_node c2_depth c2_node c2_sign))
abbrev formula_842 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_31 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

theorem normalized_812 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_32 (c0_depth c0_node c0_sign c2_depth c2_node : Int) : Prop := ((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))) ∧ ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node)))
abbrev shared_expr_Repair036_33 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))))) ∧ (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign))
theorem normalization_3188 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_842 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ ((shared_expr_Repair036_32 c0_depth c0_node c0_sign c2_depth c2_node) ∨ (shared_expr_Repair036_33 c0_depth c0_node c2_depth c2_node c2_sign)) := (or_congr (and_congr (normalization_3140 c0_depth c2_depth) (normalization_3153 c0_node c0_sign c2_node)) (and_congr (not_congr (normalization_3140 c0_depth c2_depth)) (normalization_3185 c0_depth c0_node c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair036_34 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair036_21 c0_node c2_node c2_sign)))
abbrev shared_expr_Repair036_35 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair036_4 c0_node c0_sign c2_node)) ∨ (shared_expr_Repair036_34 c0_depth c0_node c2_depth c2_node c2_sign))
abbrev shared_expr_Repair036_36 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := ((shared_expr_Repair036_35 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ ((shared_expr_Repair036_32 c0_depth c0_node c0_sign c2_depth c2_node) ∨ (shared_expr_Repair036_33 c0_depth c0_node c2_depth c2_node c2_sign)))
theorem normalization_3189 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_817 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_842 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (shared_expr_Repair036_36 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (iff_congr (normalization_3038 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (normalization_3188 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair036_37 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))))
theorem replay_2211 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_817 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_842 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_812 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) (shared_expr_Repair036_4 c0_node c0_sign c2_node) ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node)) ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair036_21 c0_node c2_node c2_sign)) (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign))
  have n0 : (shared_expr_Repair036_37 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3142 c0_depth c2_depth) (replay_2189 c0_depth c2_depth)
  have n1 : ((shared_expr_Repair036_4 c0_node c0_sign c2_node) ↔ ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node))) := by
    exact Iff.mp (normalization_3155 c0_node c0_sign c2_node) (replay_2195 c0_node c0_sign c2_node)
  have n2 : (shared_expr_Repair036_29 c0_depth c0_node c2_depth c2_node c2_sign) := by
    exact Iff.mp (normalization_3187 c0_depth c0_node c2_depth c2_node c2_sign) (replay_2210 c0_depth c0_node c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3189 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) hn

theorem normalized_813 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_38 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign)) ∨ (shared_expr_Repair036_32 c0_depth c0_node c0_sign c2_depth c2_node))
theorem normalization_3190 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_793 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_3139 c0_depth c2_depth) (normalization_3185 c0_depth c0_node c2_depth c2_node c2_sign)) (and_congr (not_congr (normalization_3139 c0_depth c2_depth)) (normalization_3153 c0_node c0_sign c2_node)))

abbrev shared_expr_Repair036_39 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((shared_expr_Repair036_32 c0_depth c0_node c0_sign c2_depth c2_node) ∨ (shared_expr_Repair036_33 c0_depth c0_node c2_depth c2_node c2_sign)) ↔ (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
theorem normalization_3191 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_842 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_793 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (shared_expr_Repair036_39 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (iff_congr (normalization_3188 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (normalization_3190 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2212 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_842 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_793 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_813 ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ((shared_expr_Repair036_0 c0_node c2_node) ∨ (shared_expr_Repair036_1 c0_node c0_sign c2_node)) (shared_expr_Repair036_27 c0_depth c0_node c2_depth c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_3191 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) hn

theorem normalized_814 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3192 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_817 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_793 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ ((shared_expr_Repair036_35 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := (iff_congr (normalization_3038 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (normalization_3190 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2213 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_817 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_793 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_814 (shared_expr_Repair036_35 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ((shared_expr_Repair036_32 c0_depth c0_node c0_sign c2_depth c2_node) ∨ (shared_expr_Repair036_33 c0_depth c0_node c2_depth c2_node c2_sign)) (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
  have n0 : (shared_expr_Repair036_36 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := by
    exact Iff.mp (normalization_3189 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (replay_2211 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)
  have n1 : (shared_expr_Repair036_39 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := by
    exact Iff.mp (normalization_3191 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (replay_2212 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3192 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair036_40 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_794 c0_node c0_sign c2_node c2_sign)) ∨ ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ∧ (formula_793 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
abbrev formula_843 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_40 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

theorem normalized_815 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_41 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair036_42 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair036_41 c0_node c0_sign c2_node c2_sign))
abbrev shared_expr_Repair036_43 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
abbrev shared_expr_Repair036_44 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair036_42 c0_node c0_sign c2_node c2_sign)) ∨ (shared_expr_Repair036_43 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
theorem normalization_3193 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_843 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_44 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_3095 c0_depth c2_depth) (normalization_3130 c0_node c0_sign c2_node c2_sign)) (and_congr (not_congr (normalization_3095 c0_depth c2_depth)) (normalization_3190 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair036_45 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair036_46 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair036_45 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair036_47 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair036_46 c0_node c0_sign c2_node c2_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_35 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
theorem normalization_3194 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_843 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ ((shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_44 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := (iff_congr (normalization_3039 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (normalization_3193 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair036_48 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))))
theorem replay_2214 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_843 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_815 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) (shared_expr_Repair036_46 c0_node c0_sign c2_node c2_sign) (shared_expr_Repair036_42 c0_node c0_sign c2_node c2_sign) (shared_expr_Repair036_35 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
  have n0 : (shared_expr_Repair036_48 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3098 c0_depth c2_depth) (replay_2167 c0_depth c2_depth)
  have n1 : ((shared_expr_Repair036_46 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Repair036_42 c0_node c0_sign c2_node c2_sign)) := by
    exact Iff.mp (normalization_3132 c0_node c0_sign c2_node c2_sign) (replay_2186 c0_node c0_sign c2_node c2_sign)
  have n2 : ((shared_expr_Repair036_35 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_3192 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (replay_2213 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3194 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) hn

theorem normalized_816 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_49 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair036_42 c0_node c0_sign c2_node c2_sign)))
theorem normalization_3195 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_3094 c0_depth c2_depth) (normalization_3190 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) (and_congr (not_congr (normalization_3094 c0_depth c2_depth)) (normalization_3130 c0_node c0_sign c2_node c2_sign)))

theorem normalization_3196 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_843 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ ((shared_expr_Repair036_44 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := (iff_congr (normalization_3193 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (normalization_3195 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2215 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_843 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_816 ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) (shared_expr_Repair036_42 c0_node c0_sign c2_node c2_sign) (shared_expr_Repair036_38 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_3196 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) hn

theorem normalized_817 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3197 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ ((shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := (iff_congr (normalization_3039 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (normalization_3195 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2216 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : ((formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
  classical
  have ht := (normalized_817 (shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (shared_expr_Repair036_44 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
  have n0 : ((shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_44 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_3194 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (replay_2214 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)
  have n1 : ((shared_expr_Repair036_44 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_3196 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (replay_2215 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3197 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) hn

abbrev shared_expr_Repair036_50 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (c2_kind = (2 : Int))) ∧ (formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ∧ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
abbrev formula_844 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_50 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_818 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∧ p2) ↔ (p1 ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3198 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ∧ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := (and_congr (normalization_1075 c2_kind) (normalization_3195 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

abbrev shared_expr_Repair036_51 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
theorem normalization_3199 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_844 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_51 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_3040 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3198 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2217 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_844 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_818 (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
  have n0 : ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_3081 c2_kind) (replay_2160 c2_kind)
  have n1 : ((shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := by
    exact Iff.mp (normalization_3197 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) (replay_2216 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3199 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair036_52 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ∧ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev formula_845 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_52 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_819 (p0 p1 : Prop) : ((p0 ∧ p1) ↔ (¬ ((¬ p0) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3200 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := (not_congr (normalization_3195 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

theorem normalization_3201 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))) ↔ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))) := (or_congr (normalization_1076 c2_kind) (normalization_3200 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

theorem normalization_3202 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))) := (not_congr (normalization_3201 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair036_53 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
theorem normalization_3203 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_845 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_53 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_3198 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3202 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2218 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_845 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_819 ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_3203 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair036_54 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (c2_kind = (2 : Int))) ∧ (formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev formula_846 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_54 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_820 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_55 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
theorem normalization_3204 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_846 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_55 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_3040 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3202 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2219 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_846 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_820 ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) (((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))))
  have n0 : (shared_expr_Repair036_51 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_3199 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2217 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have n1 : (shared_expr_Repair036_53 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_3203 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2218 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3204 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair036_56 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) ∧ (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev shared_expr_Repair036_57 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int)))))) ∨ (shared_expr_Repair036_56 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_847 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_57 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

abbrev shared_expr_Repair036_58 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((c0_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))) ↔ (formula_847 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_848 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_58 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_821 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_59 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) ∧ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev shared_expr_Repair036_60 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) ∨ (shared_expr_Repair036_59 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
theorem normalization_3205 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_847 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_60 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_481 c0_kind) (normalization_3071 c2_kind)) (and_congr (not_congr (normalization_481 c0_kind)) (normalization_3202 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair036_61 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
abbrev shared_expr_Repair036_62 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair036_61 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
theorem normalization_3206 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_848 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ ((shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_60 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (iff_congr (normalization_3041 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3205 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2220 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_848 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_821 (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair036_47 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))))
  have n0 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3067 c0_kind) (replay_2151 c0_kind)
  have n1 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3073 c2_kind) (replay_2154 c2_kind)
  have n2 : (shared_expr_Repair036_55 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_3204 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2219 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3206 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

theorem normalized_822 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_63 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ (¬ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev shared_expr_Repair036_64 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((shared_expr_Repair036_63 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ∨ ((¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))))
theorem normalization_3207 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_480 c0_kind) (normalization_3202 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) (and_congr (not_congr (normalization_480 c0_kind)) (normalization_3071 c2_kind)))

theorem normalization_3208 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : ((formula_847 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair036_60 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (iff_congr (normalization_3205 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3207 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2221 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : ((formula_847 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := by
  classical
  have ht := (normalized_822 ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Repair036_49 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))))
  have hn := ht
  exact Iff.mpr (normalization_3208 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair036_65 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((c0_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))) ↔ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_849 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_65 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_823 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3209 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_849 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ ((shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (iff_congr (normalization_3041 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3207 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2222 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_849 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_823 (shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (shared_expr_Repair036_60 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
  have n0 : ((shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_60 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := by
    exact Iff.mp (normalization_3206 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2220 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have n1 : ((shared_expr_Repair036_60 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := by
    exact Iff.mp (normalization_3208 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2221 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3209 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair036_66 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((formula_819 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∧ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
abbrev formula_850 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_66 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_824 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∧ p2) ↔ (p1 ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3210 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∧ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (and_congr (normalization_1002 c2_kind) (normalization_3207 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair036_67 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_3211 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_850 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_67 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_3042 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3210 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2223 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_850 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_824 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
  have n0 : ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_3048 c2_kind) (replay_2144 c2_kind)
  have n1 : ((shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := by
    exact Iff.mp (normalization_3209 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2222 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3211 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair036_68 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∧ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev formula_851 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_68 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_825 (p0 p1 : Prop) : ((p0 ∧ p1) ↔ (¬ ((¬ p0) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3212 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (not_congr (normalization_3207 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

theorem normalization_3213 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))) ↔ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))) := (or_congr (normalization_1003 c2_kind) (normalization_3212 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

theorem normalization_3214 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))) := (not_congr (normalization_3213 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair036_69 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
theorem normalization_3215 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_851 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_69 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_3210 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3214 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2224 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_851 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_825 ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_3215 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair036_70 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((formula_819 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev formula_852 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_70 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem normalized_826 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_71 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
theorem normalization_3216 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_852 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair036_71 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (iff_congr (normalization_3042 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (normalization_3214 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2225 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_852 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  classical
  have ht := (normalized_826 ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))))
  have n0 : (shared_expr_Repair036_67 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_3211 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2223 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have n1 : (shared_expr_Repair036_69 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_3215 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2224 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3216 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) hn

abbrev shared_expr_Repair036_72 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) ∧ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev shared_expr_Repair036_73 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∧ (formula_797 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ∨ (shared_expr_Repair036_72 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_853 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_73 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

abbrev shared_expr_Repair036_74 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_820 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_853 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_854 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_74 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_827 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_75 (c0_group c0_mode c2_group c2_mode : Int) : Prop := ((((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair036_76 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair036_75 c0_group c0_mode c2_group c2_mode)))
abbrev shared_expr_Repair036_77 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair036_76 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair036_78 (c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))))) ∧ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair036_77 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
abbrev shared_expr_Repair036_79 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) ∧ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
theorem normalization_3217 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_853 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ ((shared_expr_Repair036_78 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair036_79 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (or_congr (and_congr (normalization_379 c0_kind) (normalization_3061 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) (and_congr (not_congr (normalization_379 c0_kind)) (normalization_3214 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair036_80 (c0_group c0_mode c2_group c2_mode : Int) : Prop := (((((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair036_81 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair036_80 c0_group c0_mode c2_group c2_mode)) ∨ ((¬ (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair036_82 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair036_81 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair036_83 (c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair036_82 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
abbrev shared_expr_Repair036_84 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
abbrev shared_expr_Repair036_85 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair036_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair036_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair036_78 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair036_79 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_3218 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_854 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair036_85 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_3043 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_3217 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair036_86 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair036_82 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair036_77 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
theorem replay_2226 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_854 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_827 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair036_82 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair036_77 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair036_62 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))))
  have n0 : ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_381 c0_kind) (replay_71 c0_kind)
  have n1 : (shared_expr_Repair036_86 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := by
    exact Iff.mp (normalization_3063 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (replay_2148 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)
  have n2 : (shared_expr_Repair036_71 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
    exact Iff.mp (normalization_3216 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (replay_2225 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3218 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

abbrev shared_expr_Repair036_87 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_853 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_798 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_855 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_87 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_828 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_88 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (¬ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
theorem normalization_3219 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_798 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ ((shared_expr_Repair036_88 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ∨ (shared_expr_Repair036_78 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode)) := (or_congr (and_congr (normalization_378 c0_kind) (normalization_3214 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) (and_congr (not_congr (normalization_378 c0_kind)) (normalization_3061 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)))

abbrev shared_expr_Repair036_89 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair036_78 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair036_79 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair036_88 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ∨ (shared_expr_Repair036_78 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode)))
theorem normalization_3220 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_855 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair036_89 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_3217 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_3219 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2227 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_855 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_828 ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair036_77 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair036_64 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))))
  have hn := ht
  exact Iff.mpr (normalization_3220 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

abbrev shared_expr_Repair036_90 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_820 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_798 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_856 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_90 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_829 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair036_91 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair036_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair036_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair036_88 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ∨ (shared_expr_Repair036_78 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode)))
theorem normalization_3221 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_856 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair036_91 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_3043 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_3219 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2228 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_856 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_829 ((shared_expr_Repair036_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair036_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ((shared_expr_Repair036_78 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair036_79 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ((shared_expr_Repair036_88 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ∨ (shared_expr_Repair036_78 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode)))
  have n0 : (shared_expr_Repair036_85 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
    exact Iff.mp (normalization_3218 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2226 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)
  have n1 : (shared_expr_Repair036_89 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
    exact Iff.mp (normalization_3220 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2227 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3221 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

-- Checked replay of mp.
theorem replay_2229 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_798 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact Iff.mp (replay_2228 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2141 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157)

abbrev shared_expr_Repair036_92 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev formula_857 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_92 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

-- Checked replay of unit-resolution.
theorem replay_2230 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_857 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  exact (Or.elim (replay_2135 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (fun l0 => (Or.inl l0)) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_2229 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157)))))))

abbrev shared_expr_Repair036_93 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))) ∨ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))
abbrev formula_858 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair036_93 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem propositional_830 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 : Prop) : (((¬ p0) ∨ (¬ ((((¬ p1) ∨ (¬ p2)) ∧ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((((¬ p5) ∨ (¬ p6)) ∧ ((((¬ p7) ∨ (¬ p8)) ∧ ((¬ p9) ∨ (¬ p10) ∨ ((((¬ p11) ∨ (¬ p12)) ∧ (¬ p11)) ∨ ((¬ ((¬ p11) ∨ (¬ p12))) ∧ (¬ ((¬ p13) ∨ (¬ p14))))))) ∨ ((¬ ((¬ p7) ∨ (¬ p8))) ∧ ((((¬ p15) ∨ (¬ p16)) ∧ (¬ p16)) ∨ ((¬ ((¬ p15) ∨ (¬ p16))) ∧ (¬ ((¬ p17) ∨ (¬ p18)))))))) ∨ ((¬ ((¬ p5) ∨ (¬ p6))) ∧ ((((¬ p19) ∨ (¬ p20)) ∧ (¬ p20)) ∨ ((¬ ((¬ p19) ∨ (¬ p20))) ∧ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ p13) ∨ (¬ p14))))))))))) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ (¬ ((¬ p21) ∨ (¬ p22))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2231 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_858 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  exact (propositional_830 ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) (c0_kind ≤ (2 : Int)) (c0_kind ≥ (2 : Int)) (c2_kind ≤ (2 : Int)) (c2_kind ≥ (2 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2232 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))) := by
  exact (Or.elim (replay_2231 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i158 t0))))

-- Checked replay of unit-resolution.
theorem replay_2233 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) := by
  exact (Or.elim (replay_2230 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_2232 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign i158)))))

-- Checked replay of unit-resolution.
theorem replay_2234 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (c0_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_2134 c0_kind) (fun l0 => (False.elim ((replay_2233 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i158) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2235 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (¬ (c0_kind ≥ (1 : Int))) := by
  exact (Or.elim (replay_2133 c0_kind) (fun l0 => (False.elim (l0 (replay_2234 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i158)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2236 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (¬ (formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  exact (Or.elim (replay_2132 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154) (fun l0 => (False.elim ((replay_2235 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i158) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2237 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i158 : (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) : (c0_mode ≥ (0 : Int)) := by
  exact (Or.elim (replay_2112 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (fun l0 => (False.elim ((replay_2236 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i154 i157 i158) l0))) (fun t0 => t0))

abbrev shared_expr_Repair036_94 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (formula_78 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∨ (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign))
abbrev formula_859 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair036_94 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign)

theorem propositional_831 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 : Prop) : ((¬ ((p0 ∧ ((((¬ p1) ∨ (¬ ((¬ p2) ∨ (¬ p3)))) ∧ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9))) ∨ ((¬ ((¬ p1) ∨ (¬ ((¬ p2) ∨ (¬ p3))))) ∧ ((¬ ((¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16))) ∨ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ p19) ∨ (¬ p20) ∨ (¬ p21) ∨ (¬ p22) ∨ (¬ p16))) ∨ (¬ (p17 ∨ p23 ∨ (¬ p24) ∨ (¬ p25) ∨ (¬ p26) ∨ (¬ p27))))))) ∨ (¬ ((¬ p28) ∨ (¬ p29) ∨ (¬ ((¬ ((¬ p14) ∨ (¬ p15) ∨ (¬ p30) ∨ (¬ p31))) ∨ (¬ (p32 ∨ (¬ p26) ∨ (¬ p27) ∨ (¬ p33))))))))))) ∨ ((¬ p0) ∧ p34))) ∨ p0 ∨ p34) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2238 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_859 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign) := by
  exact (propositional_831 ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) (c0_kind ≤ (2 : Int)) (c0_kind ≥ (2 : Int)) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) (c0_sign ≤ (2 : Int)) (c0_sign ≥ (2 : Int)) ((r2_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (c0_sign ≤ (1 : Int)) (c0_sign ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((c0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) ((c0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign))

abbrev shared_expr_Repair036_95 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) ∨ (formula_78 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign) ∨ (¬ (formula_79 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)))
abbrev formula_860 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair036_95 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem propositional_832 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 : Prop) : ((¬ p0) ∨ p1 ∨ (¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((p2 ∧ ((¬ ((¬ p3) ∨ (¬ p4) ∨ (¬ ((p5 ∧ (¬ p6)) ∨ ((¬ p5) ∧ (¬ p7)))))) ∨ (¬ ((¬ p8) ∨ (¬ p9) ∨ (¬ ((p5 ∧ (¬ p10)) ∨ ((¬ p5) ∧ (¬ p7)))))) ∨ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ ((p5 ∧ (¬ ((¬ p13) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p18)))) ∨ ((¬ p5) ∧ (¬ p6)))))) ∨ (¬ ((¬ p19) ∨ (¬ p20) ∨ (¬ ((p5 ∧ (¬ ((¬ p13) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p17) ∨ (¬ p18)))) ∨ ((¬ p5) ∧ (¬ p6)))))) ∨ (¬ ((¬ p22) ∨ (¬ p23) ∨ (¬ ((p5 ∧ (¬ p10)) ∨ ((¬ p5) ∧ (¬ ((¬ p13) ∨ (¬ p14) ∨ (¬ p24) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p18)))))))) ∨ (¬ ((¬ p25) ∨ (¬ p26) ∨ (¬ ((p5 ∧ (¬ p10)) ∨ ((¬ p5) ∧ (¬ ((¬ p13) ∨ (¬ p14) ∨ (¬ p24) ∨ (¬ p21) ∨ (¬ p17) ∨ (¬ p18)))))))))) ∨ ((¬ p2) ∧ (¬ ((¬ p27) ∨ (¬ p28) ∨ (¬ p29) ∨ (¬ p30) ∨ (¬ ((¬ p31) ∨ (¬ p32))))))))))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2239 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_860 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (propositional_832 ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) (formula_78 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign) ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) (r2_mode ≤ (0 : Int)) (r2_mode ≥ (0 : Int)) ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (formula_39 c0_depth c0_kind c0_sign r2_level) ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) (r2_mode ≤ (1 : Int)) (r2_mode ≥ (1 : Int)) (formula_41 c0_depth c0_kind c0_sign r2_level) (r2_mode ≤ (2 : Int)) (r2_mode ≥ (2 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ((c0_node % (2 : Int)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) (r2_mode ≤ (3 : Int)) (r2_mode ≥ (3 : Int)) ((c0_node % (2 : Int)) ≥ (1 : Int)) (r2_mode ≤ (4 : Int)) (r2_mode ≥ (4 : Int)) ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) (r2_mode ≤ (5 : Int)) (r2_mode ≥ (5 : Int)) ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2240 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i9 : ((formula_100 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : ((¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) ∨ (formula_78 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_2239 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (Or.inl l0)) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_111 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i9)))))))

theorem propositional_833 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2241 (h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : ((formula_36 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ∨ (r2_depth ≤ (0 : Int))) := by
  exact (propositional_833 (r2_mode ≥ (6 : Int)) (r2_mode ≥ (0 : Int)) (r2_depth ≤ (0 : Int)) (r2_depth ≥ (0 : Int)) (r2_node ≤ (0 : Int)) (r2_node ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_kind ≤ (0 : Int)) (r2_kind ≥ (0 : Int)) (r2_level ≥ (1 : Int)) ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int)) (r2_group ≤ (1 : Int)) (r2_group ≥ (1 : Int)) (r2_group ≤ (2 : Int)) (r2_group ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_2242 (c0_level r2_depth : Int) : ((¬ (c0_level ≥ (0 : Int))) ∨ (¬ (r2_depth ≤ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_2243 (c0_level : Int) : ((c0_level ≥ (0 : Int)) ∨ (¬ (c0_level ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_834 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p10) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2244 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (c0_level ≥ (1 : Int))) := by
  exact (propositional_834 (c0_mode ≥ (6 : Int)) (c0_mode ≥ (0 : Int)) (c0_depth ≤ (0 : Int)) (c0_depth ≥ (0 : Int)) (c0_node ≤ (0 : Int)) (c0_node ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) (c0_kind ≤ (0 : Int)) (c0_kind ≥ (0 : Int)) (c0_level ≥ (1 : Int)) ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (c0_group ≤ (2 : Int)) (c0_group ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2245 (c0_kind : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) : (c0_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_2134 c0_kind) (fun l0 => (False.elim (i12 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2246 (c0_kind : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) : (¬ (c0_kind ≥ (1 : Int))) := by
  exact (Or.elim (replay_2133 c0_kind) (fun l0 => (False.elim (l0 (replay_2245 c0_kind i12)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2247 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) : (¬ (formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  exact (Or.elim (replay_2132 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154) (fun l0 => (False.elim ((replay_2246 c0_kind i12) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2248 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) : (c0_level ≥ (1 : Int)) := by
  exact (Or.elim (replay_2244 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (fun l0 => (False.elim ((replay_2247 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154 i12) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2249 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) : (c0_level ≥ (0 : Int)) := by
  exact (Or.elim (replay_2243 c0_level) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_2248 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154 i12)))))

-- Checked replay of unit-resolution.
theorem replay_2250 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i159 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)))) : (¬ (r2_depth ≤ (0 : Int))) := by
  exact (Or.elim (replay_2242 c0_level r2_depth) (fun l0 => (False.elim (l0 (replay_2249 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154 i12)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (i159 t1))))))

-- Checked replay of unit-resolution.
theorem replay_2251 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i159 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)))) : (formula_36 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (Or.elim (replay_2241 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_2250 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth i154 i12 i159) t0))))

-- Checked replay of unit-resolution.
theorem replay_2252 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i159 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)))) : (formula_159 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (Or.elim (replay_1203 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_2250 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth i154 i12 i159) t0))))

end H4Formal.Generated.Repair
