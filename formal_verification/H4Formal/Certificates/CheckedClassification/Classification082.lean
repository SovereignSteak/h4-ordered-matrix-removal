import H4Formal.Certificates.CheckedClassification.Classification081

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Classification082_0 (c2_node c3_node : Int) : Prop := (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2219 (c2_node c3_node : Int) : Prop := (shared_expr_Classification082_0 c2_node c3_node)

theorem normalized_1907 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_1 (c2_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
theorem normalization_7351 (c2_node c3_node : Int) : (formula_2219 c2_node c3_node) ↔ (shared_expr_Classification082_1 c2_node c3_node) := (iff_congr (normalization_7244 c2_node c3_node) (normalization_7349 c2_node c3_node))

-- Checked replay of trans.
abbrev shared_expr_Classification082_2 (c2_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem replay_5137 (c2_node c3_node : Int) : (formula_2219 c2_node c3_node) := by
  classical
  have ht := (normalized_1907 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) (shared_expr_Classification082_1 c2_node c3_node))
  have n0 : (shared_expr_Classification082_2 c2_node c3_node) := by
    exact Iff.mp (normalization_7346 c2_node c3_node) (replay_5135 c2_node c3_node)
  have n1 : (shared_expr_Classification082_1 c2_node c3_node) := by
    exact Iff.mp (normalization_7350 c2_node c3_node) (replay_5136 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7351 c2_node c3_node) hn

abbrev shared_expr_Classification082_3 (c2_node c2_sign c3_node : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))))
abbrev shared_expr_Classification082_4 (c2_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2220 (c2_node c2_sign c3_node : Int) : Prop := ((shared_expr_Classification082_3 c2_node c2_sign c3_node) ∨ (shared_expr_Classification082_4 c2_node c3_node))

theorem normalized_1908 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_5 (c2_node c2_sign c3_node : Int) : Prop := ((¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Classification082_6 (c2_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_7352 (c2_node c2_sign c3_node : Int) : (formula_2220 c2_node c2_sign c3_node) ↔ ((shared_expr_Classification082_5 c2_node c2_sign c3_node) ∨ (shared_expr_Classification082_6 c2_node c3_node)) := (or_congr (and_congr (normalization_7349 c2_node c3_node) (normalization_976 c2_sign)) (and_congr (not_congr (normalization_7349 c2_node c3_node)) (normalization_7246 c2_node c3_node)))

abbrev shared_expr_Classification082_7 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification082_8 (c2_node c2_sign c3_node : Int) : Prop := ((((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Classification082_7 c2_node c3_node))
theorem normalization_7353 (c2_node c2_sign c3_node : Int) : ((formula_2202 c2_node c2_sign c3_node) ↔ (formula_2220 c2_node c2_sign c3_node)) ↔ ((shared_expr_Classification082_8 c2_node c2_sign c3_node) ↔ ((shared_expr_Classification082_5 c2_node c2_sign c3_node) ∨ (shared_expr_Classification082_6 c2_node c3_node))) := (iff_congr (normalization_7247 c2_node c2_sign c3_node) (normalization_7352 c2_node c2_sign c3_node))

-- Checked replay of monotonicity.
theorem replay_5138 (c2_node c2_sign c3_node : Int) : ((formula_2202 c2_node c2_sign c3_node) ↔ (formula_2220 c2_node c2_sign c3_node)) := by
  classical
  have ht := (normalized_1908 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Classification082_1 c2_node c3_node) := by
    exact Iff.mp (normalization_7351 c2_node c3_node) (replay_5137 c2_node c3_node)
  have n1 : ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1114 c2_sign) (replay_519 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7353 c2_node c2_sign c3_node) hn

theorem normalized_1909 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_9 (c2_node c3_node : Int) : Prop := (((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_7354 (c2_node c2_sign c3_node : Int) : (formula_2176 c2_node c2_sign c3_node) ↔ ((shared_expr_Classification082_9 c2_node c3_node) ∨ (shared_expr_Classification082_5 c2_node c2_sign c3_node)) := (or_congr (and_congr (normalization_7348 c2_node c3_node) (normalization_7246 c2_node c3_node)) (and_congr (not_congr (normalization_7348 c2_node c3_node)) (normalization_976 c2_sign)))

abbrev shared_expr_Classification082_10 (c2_node c2_sign c3_node : Int) : Prop := (((shared_expr_Classification082_5 c2_node c2_sign c3_node) ∨ (shared_expr_Classification082_6 c2_node c3_node)) ↔ ((shared_expr_Classification082_9 c2_node c3_node) ∨ (shared_expr_Classification082_5 c2_node c2_sign c3_node)))
theorem normalization_7355 (c2_node c2_sign c3_node : Int) : ((formula_2220 c2_node c2_sign c3_node) ↔ (formula_2176 c2_node c2_sign c3_node)) ↔ (shared_expr_Classification082_10 c2_node c2_sign c3_node) := (iff_congr (normalization_7352 c2_node c2_sign c3_node) (normalization_7354 c2_node c2_sign c3_node))

-- Checked replay of rewrite.
theorem replay_5139 (c2_node c2_sign c3_node : Int) : ((formula_2220 c2_node c2_sign c3_node) ↔ (formula_2176 c2_node c2_sign c3_node)) := by
  classical
  have ht := (normalized_1909 ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7355 c2_node c2_sign c3_node) hn

theorem normalized_1910 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7356 (c2_node c2_sign c3_node : Int) : ((formula_2202 c2_node c2_sign c3_node) ↔ (formula_2176 c2_node c2_sign c3_node)) ↔ ((shared_expr_Classification082_8 c2_node c2_sign c3_node) ↔ ((shared_expr_Classification082_9 c2_node c3_node) ∨ (shared_expr_Classification082_5 c2_node c2_sign c3_node))) := (iff_congr (normalization_7247 c2_node c2_sign c3_node) (normalization_7354 c2_node c2_sign c3_node))

-- Checked replay of trans.
theorem replay_5140 (c2_node c2_sign c3_node : Int) : ((formula_2202 c2_node c2_sign c3_node) ↔ (formula_2176 c2_node c2_sign c3_node)) := by
  classical
  have ht := (normalized_1910 (shared_expr_Classification082_8 c2_node c2_sign c3_node) ((shared_expr_Classification082_5 c2_node c2_sign c3_node) ∨ (shared_expr_Classification082_6 c2_node c3_node)) ((shared_expr_Classification082_9 c2_node c3_node) ∨ (shared_expr_Classification082_5 c2_node c2_sign c3_node)))
  have n0 : ((shared_expr_Classification082_8 c2_node c2_sign c3_node) ↔ ((shared_expr_Classification082_5 c2_node c2_sign c3_node) ∨ (shared_expr_Classification082_6 c2_node c3_node))) := by
    exact Iff.mp (normalization_7353 c2_node c2_sign c3_node) (replay_5138 c2_node c2_sign c3_node)
  have n1 : (shared_expr_Classification082_10 c2_node c2_sign c3_node) := by
    exact Iff.mp (normalization_7355 c2_node c2_sign c3_node) (replay_5139 c2_node c2_sign c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7356 c2_node c2_sign c3_node) hn

theorem normalized_1911 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7357 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_7358 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_7359 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (and_congr (normalization_7357 c2_depth c3_depth) (normalization_7358 c2_depth c3_depth))

abbrev shared_expr_Classification082_11 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
theorem normalization_7360 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification082_11 c2_depth c3_depth) := (iff_congr (normalization_7248 c2_depth c3_depth) (normalization_7359 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5141 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1911 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7360 c2_depth c3_depth) hn

abbrev shared_expr_Classification082_12 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))
abbrev formula_2221 (c2_depth c3_depth : Int) : Prop := (shared_expr_Classification082_12 c2_depth c3_depth)

theorem normalized_1912 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7361 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := (not_congr (normalization_7357 c2_depth c3_depth))

theorem normalization_7362 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (not_congr (normalization_7358 c2_depth c3_depth))

theorem normalization_7363 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) := (or_congr (normalization_7361 c2_depth c3_depth) (normalization_7362 c2_depth c3_depth))

theorem normalization_7364 (c2_depth c3_depth : Int) : (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))) := (not_congr (normalization_7363 c2_depth c3_depth))

abbrev shared_expr_Classification082_13 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))))
theorem normalization_7365 (c2_depth c3_depth : Int) : (formula_2221 c2_depth c3_depth) ↔ (shared_expr_Classification082_13 c2_depth c3_depth) := (iff_congr (normalization_7359 c2_depth c3_depth) (normalization_7364 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5142 (c2_depth c3_depth : Int) : (formula_2221 c2_depth c3_depth) := by
  classical
  have ht := (normalized_1912 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7365 c2_depth c3_depth) hn

theorem normalized_1913 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7366 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification082_13 c2_depth c3_depth) := (iff_congr (normalization_7248 c2_depth c3_depth) (normalization_7364 c2_depth c3_depth))

-- Checked replay of trans.
theorem replay_5143 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1913 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (shared_expr_Classification082_13 c2_depth c3_depth))
  have n0 : (shared_expr_Classification082_11 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7360 c2_depth c3_depth) (replay_5141 c2_depth c3_depth)
  have n1 : (shared_expr_Classification082_13 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7365 c2_depth c3_depth) (replay_5142 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7366 c2_depth c3_depth) hn

theorem normalized_1914 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7367 (c2_depth c3_depth : Int) : (¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))) := (not_congr (normalization_7364 c2_depth c3_depth))

abbrev shared_expr_Classification082_14 (c2_depth c3_depth : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ (¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))))
theorem normalization_7368 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))) ↔ (shared_expr_Classification082_14 c2_depth c3_depth) := (iff_congr (normalization_7249 c2_depth c3_depth) (normalization_7367 c2_depth c3_depth))

-- Checked replay of monotonicity.
theorem replay_5144 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_1914 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification082_13 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7366 c2_depth c3_depth) (replay_5143 c2_depth c3_depth)
  have hn := ht n0
  exact Iff.mpr (normalization_7368 c2_depth c3_depth) hn

abbrev shared_expr_Classification082_15 (c2_depth c3_depth : Int) : Prop := ((¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))
abbrev formula_2222 (c2_depth c3_depth : Int) : Prop := (shared_expr_Classification082_15 c2_depth c3_depth)

theorem normalized_1915 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_16 (c2_depth c3_depth : Int) : Prop := ((¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
theorem normalization_7369 (c2_depth c3_depth : Int) : (formula_2222 c2_depth c3_depth) ↔ (shared_expr_Classification082_16 c2_depth c3_depth) := (iff_congr (normalization_7367 c2_depth c3_depth) (normalization_7363 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5145 (c2_depth c3_depth : Int) : (formula_2222 c2_depth c3_depth) := by
  classical
  have ht := (normalized_1915 ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_7369 c2_depth c3_depth) hn

theorem normalized_1916 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_17 (c2_depth c3_depth : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
theorem normalization_7370 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (shared_expr_Classification082_17 c2_depth c3_depth) := (iff_congr (normalization_7249 c2_depth c3_depth) (normalization_7363 c2_depth c3_depth))

-- Checked replay of trans.
theorem replay_5146 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) := by
  classical
  have ht := (normalized_1916 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification082_14 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7368 c2_depth c3_depth) (replay_5144 c2_depth c3_depth)
  have n1 : (shared_expr_Classification082_16 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7369 c2_depth c3_depth) (replay_5145 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7370 c2_depth c3_depth) hn

theorem normalized_1917 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7371 (c2_node c3_node : Int) : ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7372 (c2_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (and_congr (normalization_7251 c2_node c3_node) (normalization_7371 c2_node c3_node))

abbrev shared_expr_Classification082_18 (c2_node c3_node : Int) : Prop := (((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
theorem normalization_7373 (c2_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification082_18 c2_node c3_node) := (iff_congr (normalization_7250 c2_node c3_node) (normalization_7372 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_5147 (c2_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1917 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_7373 c2_node c3_node) hn

abbrev shared_expr_Classification082_19 (c2_node c3_node : Int) : Prop := ((((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2223 (c2_node c3_node : Int) : Prop := (shared_expr_Classification082_19 c2_node c3_node)

theorem normalized_1918 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7374 (c2_node c3_node : Int) : (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_7371 c2_node c3_node))

theorem normalization_7375 (c2_node c3_node : Int) : ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) := (or_congr (normalization_7252 c2_node c3_node) (normalization_7374 c2_node c3_node))

theorem normalization_7376 (c2_node c3_node : Int) : (¬ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) := (not_congr (normalization_7375 c2_node c3_node))

abbrev shared_expr_Classification082_20 (c2_node c3_node : Int) : Prop := (((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))))
theorem normalization_7377 (c2_node c3_node : Int) : (formula_2223 c2_node c3_node) ↔ (shared_expr_Classification082_20 c2_node c3_node) := (iff_congr (normalization_7372 c2_node c3_node) (normalization_7376 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_5148 (c2_node c3_node : Int) : (formula_2223 c2_node c3_node) := by
  classical
  have ht := (normalized_1918 (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7377 c2_node c3_node) hn

abbrev shared_expr_Classification082_21 (c2_node c3_node : Int) : Prop := (((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2224 (c2_node c3_node : Int) : Prop := (shared_expr_Classification082_21 c2_node c3_node)

theorem normalized_1919 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7378 (c2_node c3_node : Int) : (formula_2224 c2_node c3_node) ↔ (shared_expr_Classification082_20 c2_node c3_node) := (iff_congr (normalization_7250 c2_node c3_node) (normalization_7376 c2_node c3_node))

-- Checked replay of trans.
theorem replay_5149 (c2_node c3_node : Int) : (formula_2224 c2_node c3_node) := by
  classical
  have ht := (normalized_1919 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) (shared_expr_Classification082_20 c2_node c3_node))
  have n0 : (shared_expr_Classification082_18 c2_node c3_node) := by
    exact Iff.mp (normalization_7373 c2_node c3_node) (replay_5147 c2_node c3_node)
  have n1 : (shared_expr_Classification082_20 c2_node c3_node) := by
    exact Iff.mp (normalization_7377 c2_node c3_node) (replay_5148 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7378 c2_node c3_node) hn

abbrev shared_expr_Classification082_22 (c2_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification082_23 (c2_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_2225 (c2_node c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_22 c2_node c3_node c3_sign) ∨ (shared_expr_Classification082_23 c2_node c3_node))

theorem normalized_1920 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_24 (c2_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification082_25 (c2_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))))) ∧ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_7379 (c2_node c3_node c3_sign : Int) : (formula_2225 c2_node c3_node c3_sign) ↔ ((shared_expr_Classification082_24 c2_node c3_node c3_sign) ∨ (shared_expr_Classification082_25 c2_node c3_node)) := (or_congr (and_congr (normalization_7376 c2_node c3_node) (normalization_6849 c3_sign)) (and_congr (not_congr (normalization_7376 c2_node c3_node)) (normalization_7252 c2_node c3_node)))

abbrev shared_expr_Classification082_26 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification082_27 (c2_node c3_node c3_sign : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification082_26 c2_node c3_node))
theorem normalization_7380 (c2_node c3_node c3_sign : Int) : ((formula_2203 c2_node c3_node c3_sign) ↔ (formula_2225 c2_node c3_node c3_sign)) ↔ ((shared_expr_Classification082_27 c2_node c3_node c3_sign) ↔ ((shared_expr_Classification082_24 c2_node c3_node c3_sign) ∨ (shared_expr_Classification082_25 c2_node c3_node))) := (iff_congr (normalization_7253 c2_node c3_node c3_sign) (normalization_7379 c2_node c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5150 (c2_node c3_node c3_sign : Int) : ((formula_2203 c2_node c3_node c3_sign) ↔ (formula_2225 c2_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_1920 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification082_20 c2_node c3_node) := by
    exact Iff.mp (normalization_7378 c2_node c3_node) (replay_5149 c2_node c3_node)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6942 c3_sign) (replay_4980 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7380 c2_node c3_node c3_sign) hn

theorem normalized_1921 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_28 (c2_node c3_node : Int) : Prop := (((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_7381 (c2_node c3_node c3_sign : Int) : (formula_2175 c2_node c3_node c3_sign) ↔ ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign)) := (or_congr (and_congr (normalization_7375 c2_node c3_node) (normalization_7252 c2_node c3_node)) (and_congr (not_congr (normalization_7375 c2_node c3_node)) (normalization_6849 c3_sign)))

abbrev shared_expr_Classification082_29 (c2_node c3_node c3_sign : Int) : Prop := (((shared_expr_Classification082_24 c2_node c3_node c3_sign) ∨ (shared_expr_Classification082_25 c2_node c3_node)) ↔ ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign)))
theorem normalization_7382 (c2_node c3_node c3_sign : Int) : ((formula_2225 c2_node c3_node c3_sign) ↔ (formula_2175 c2_node c3_node c3_sign)) ↔ (shared_expr_Classification082_29 c2_node c3_node c3_sign) := (iff_congr (normalization_7379 c2_node c3_node c3_sign) (normalization_7381 c2_node c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5151 (c2_node c3_node c3_sign : Int) : ((formula_2225 c2_node c3_node c3_sign) ↔ (formula_2175 c2_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_1921 ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7382 c2_node c3_node c3_sign) hn

theorem normalized_1922 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7383 (c2_node c3_node c3_sign : Int) : ((formula_2203 c2_node c3_node c3_sign) ↔ (formula_2175 c2_node c3_node c3_sign)) ↔ ((shared_expr_Classification082_27 c2_node c3_node c3_sign) ↔ ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign))) := (iff_congr (normalization_7253 c2_node c3_node c3_sign) (normalization_7381 c2_node c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5152 (c2_node c3_node c3_sign : Int) : ((formula_2203 c2_node c3_node c3_sign) ↔ (formula_2175 c2_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_1922 (shared_expr_Classification082_27 c2_node c3_node c3_sign) ((shared_expr_Classification082_24 c2_node c3_node c3_sign) ∨ (shared_expr_Classification082_25 c2_node c3_node)) ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign)))
  have n0 : ((shared_expr_Classification082_27 c2_node c3_node c3_sign) ↔ ((shared_expr_Classification082_24 c2_node c3_node c3_sign) ∨ (shared_expr_Classification082_25 c2_node c3_node))) := by
    exact Iff.mp (normalization_7380 c2_node c3_node c3_sign) (replay_5150 c2_node c3_node c3_sign)
  have n1 : (shared_expr_Classification082_29 c2_node c3_node c3_sign) := by
    exact Iff.mp (normalization_7382 c2_node c3_node c3_sign) (replay_5151 c2_node c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7383 c2_node c3_node c3_sign) hn

abbrev shared_expr_Classification082_30 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_2203 c2_node c3_node c3_sign)) ↔ (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_2175 c2_node c3_node c3_sign)))
abbrev formula_2226 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_30 c2_depth c2_node c3_depth c3_node c3_sign)

theorem normalized_1923 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_31 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign)))
theorem normalization_7384 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_2175 c2_node c3_node c3_sign)) ↔ (shared_expr_Classification082_31 c2_depth c2_node c3_depth c3_node c3_sign) := (or_congr (normalization_7363 c2_depth c3_depth) (normalization_7381 c2_node c3_node c3_sign))

abbrev shared_expr_Classification082_32 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification082_27 c2_node c3_node c3_sign)) ↔ (shared_expr_Classification082_31 c2_depth c2_node c3_depth c3_node c3_sign))
theorem normalization_7385 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (formula_2226 c2_depth c2_node c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_32 c2_depth c2_node c3_depth c3_node c3_sign) := (iff_congr (normalization_7254 c2_depth c2_node c3_depth c3_node c3_sign) (normalization_7384 c2_depth c2_node c3_depth c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5153 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (formula_2226 c2_depth c2_node c3_depth c3_node c3_sign) := by
  classical
  have ht := (normalized_1923 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) (shared_expr_Classification082_27 c2_node c3_node c3_sign) ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign)))
  have n0 : (shared_expr_Classification082_17 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7370 c2_depth c3_depth) (replay_5146 c2_depth c3_depth)
  have n1 : ((shared_expr_Classification082_27 c2_node c3_node c3_sign) ↔ ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign))) := by
    exact Iff.mp (normalization_7383 c2_node c3_node c3_sign) (replay_5152 c2_node c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7385 c2_depth c2_node c3_depth c3_node c3_sign) hn

abbrev shared_expr_Classification082_33 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_2175 c2_node c3_node c3_sign)) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_2175 c2_node c3_node c3_sign)))
abbrev formula_2227 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_33 c2_depth c2_node c3_depth c3_node c3_sign)

theorem normalized_1924 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_34 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ∨ ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign)))
theorem normalization_7386 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_2175 c2_node c3_node c3_sign)) ↔ (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign) := (or_congr (normalization_7361 c2_depth c3_depth) (or_congr (normalization_7362 c2_depth c3_depth) (normalization_7381 c2_node c3_node c3_sign)))

theorem normalization_7387 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (formula_2227 c2_depth c2_node c3_depth c3_node c3_sign) ↔ ((shared_expr_Classification082_31 c2_depth c2_node c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign)) := (iff_congr (normalization_7384 c2_depth c2_node c3_depth c3_node c3_sign) (normalization_7386 c2_depth c2_node c3_depth c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5154 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (formula_2227 c2_depth c2_node c3_depth c3_node c3_sign) := by
  classical
  have ht := (normalized_1924 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((shared_expr_Classification082_28 c2_node c3_node) ∨ (shared_expr_Classification082_24 c2_node c3_node c3_sign)))
  have hn := ht
  exact Iff.mpr (normalization_7387 c2_depth c2_node c3_depth c3_node c3_sign) hn

abbrev shared_expr_Classification082_35 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_2203 c2_node c3_node c3_sign)) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_2175 c2_node c3_node c3_sign)))
abbrev formula_2228 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_35 c2_depth c2_node c3_depth c3_node c3_sign)

theorem normalized_1925 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_36 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification082_27 c2_node c3_node c3_sign)) ↔ (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign))
theorem normalization_7388 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (formula_2228 c2_depth c2_node c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_36 c2_depth c2_node c3_depth c3_node c3_sign) := (iff_congr (normalization_7254 c2_depth c2_node c3_depth c3_node c3_sign) (normalization_7386 c2_depth c2_node c3_depth c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5155 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (formula_2228 c2_depth c2_node c3_depth c3_node c3_sign) := by
  classical
  have ht := (normalized_1925 ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification082_27 c2_node c3_node c3_sign)) (shared_expr_Classification082_31 c2_depth c2_node c3_depth c3_node c3_sign) (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign))
  have n0 : (shared_expr_Classification082_32 c2_depth c2_node c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_7385 c2_depth c2_node c3_depth c3_node c3_sign) (replay_5153 c2_depth c2_node c3_depth c3_node c3_sign)
  have n1 : ((shared_expr_Classification082_31 c2_depth c2_node c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_7387 c2_depth c2_node c3_depth c3_node c3_sign) (replay_5154 c2_depth c2_node c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7388 c2_depth c2_node c3_depth c3_node c3_sign) hn

abbrev shared_expr_Classification082_37 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) ∧ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_2175 c2_node c3_node c3_sign)))
abbrev shared_expr_Classification082_38 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ∧ (formula_2176 c2_node c2_sign c3_node)) ∨ (shared_expr_Classification082_37 c2_depth c2_node c3_depth c3_node c3_sign))
abbrev formula_2229 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_38 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

theorem normalized_1926 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_39 (c2_depth c2_node c2_sign c3_depth c3_node : Int) : Prop := ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))) ∧ ((shared_expr_Classification082_9 c2_node c3_node) ∨ (shared_expr_Classification082_5 c2_node c2_sign c3_node)))
abbrev shared_expr_Classification082_40 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))))) ∧ (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign))
theorem normalization_7389 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2229 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ ((shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node) ∨ (shared_expr_Classification082_40 c2_depth c2_node c3_depth c3_node c3_sign)) := (or_congr (and_congr (normalization_7341 c2_depth c3_depth) (normalization_7354 c2_node c2_sign c3_node)) (and_congr (not_congr (normalization_7341 c2_depth c3_depth)) (normalization_7386 c2_depth c2_node c3_depth c3_node c3_sign)))

abbrev shared_expr_Classification082_41 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification082_27 c2_node c3_node c3_sign)))
abbrev shared_expr_Classification082_42 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification082_8 c2_node c2_sign c3_node)) ∨ (shared_expr_Classification082_41 c2_depth c2_node c3_depth c3_node c3_sign))
abbrev shared_expr_Classification082_43 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_42 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ ((shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node) ∨ (shared_expr_Classification082_40 c2_depth c2_node c3_depth c3_node c3_sign)))
theorem normalization_7390 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2204 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2229 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (shared_expr_Classification082_43 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (iff_congr (normalization_7255 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (normalization_7389 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification082_44 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))))
theorem replay_5156 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2204 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2229 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_1926 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) (shared_expr_Classification082_8 c2_node c2_sign c3_node) ((shared_expr_Classification082_9 c2_node c3_node) ∨ (shared_expr_Classification082_5 c2_node c2_sign c3_node)) ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification082_27 c2_node c3_node c3_sign)) (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign))
  have n0 : (shared_expr_Classification082_44 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7343 c2_depth c3_depth) (replay_5134 c2_depth c3_depth)
  have n1 : ((shared_expr_Classification082_8 c2_node c2_sign c3_node) ↔ ((shared_expr_Classification082_9 c2_node c3_node) ∨ (shared_expr_Classification082_5 c2_node c2_sign c3_node))) := by
    exact Iff.mp (normalization_7356 c2_node c2_sign c3_node) (replay_5140 c2_node c2_sign c3_node)
  have n2 : (shared_expr_Classification082_36 c2_depth c2_node c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_7388 c2_depth c2_node c3_depth c3_node c3_sign) (replay_5155 c2_depth c2_node c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_7390 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) hn

theorem normalized_1927 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_45 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign))
theorem normalization_7391 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2177 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ ((shared_expr_Classification082_45 c2_depth c2_node c3_depth c3_node c3_sign) ∨ (shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node)) := (or_congr (and_congr (normalization_7340 c2_depth c3_depth) (normalization_7386 c2_depth c2_node c3_depth c3_node c3_sign)) (and_congr (not_congr (normalization_7340 c2_depth c3_depth)) (normalization_7354 c2_node c2_sign c3_node)))

abbrev shared_expr_Classification082_46 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node) ∨ (shared_expr_Classification082_40 c2_depth c2_node c3_depth c3_node c3_sign)) ↔ ((shared_expr_Classification082_45 c2_depth c2_node c3_depth c3_node c3_sign) ∨ (shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node)))
theorem normalization_7392 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2229 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2177 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (shared_expr_Classification082_46 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (iff_congr (normalization_7389 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (normalization_7391 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5157 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2229 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2177 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_1927 ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ((shared_expr_Classification082_9 c2_node c3_node) ∨ (shared_expr_Classification082_5 c2_node c2_sign c3_node)) (shared_expr_Classification082_34 c2_depth c2_node c3_depth c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7392 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) hn

theorem normalized_1928 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_47 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_42 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ ((shared_expr_Classification082_45 c2_depth c2_node c3_depth c3_node c3_sign) ∨ (shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node)))
theorem normalization_7393 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2204 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2177 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (shared_expr_Classification082_47 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (iff_congr (normalization_7255 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (normalization_7391 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5158 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2204 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2177 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_1928 (shared_expr_Classification082_42 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ((shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node) ∨ (shared_expr_Classification082_40 c2_depth c2_node c3_depth c3_node c3_sign)) ((shared_expr_Classification082_45 c2_depth c2_node c3_depth c3_node c3_sign) ∨ (shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node)))
  have n0 : (shared_expr_Classification082_43 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_7390 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (replay_5156 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)
  have n1 : (shared_expr_Classification082_46 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_7392 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (replay_5157 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7393 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) hn

abbrev shared_expr_Classification082_48 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ∧ (formula_2178 c2_node c2_sign c3_node c3_sign)) ∨ ((¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ∧ (formula_2177 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev formula_2230 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_48 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

theorem normalized_1929 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_49 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification082_50 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Classification082_49 c2_node c2_sign c3_node c3_sign))
abbrev shared_expr_Classification082_51 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))))) ∧ ((shared_expr_Classification082_45 c2_depth c2_node c3_depth c3_node c3_sign) ∨ (shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node)))
abbrev shared_expr_Classification082_52 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification082_50 c2_node c2_sign c3_node c3_sign)) ∨ (shared_expr_Classification082_51 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
theorem normalization_7394 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2230 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_52 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7304 c2_depth c3_depth) (normalization_7331 c2_node c2_sign c3_node c3_sign)) (and_congr (not_congr (normalization_7304 c2_depth c3_depth)) (normalization_7391 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

abbrev shared_expr_Classification082_53 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification082_54 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_53 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification082_55 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_42 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
abbrev shared_expr_Classification082_56 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification082_54 c2_node c2_sign c3_node c3_sign)) ∨ (shared_expr_Classification082_55 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
theorem normalization_7395 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2230 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ ((shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_52 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (iff_congr (normalization_7256 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (normalization_7394 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification082_57 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))))
theorem replay_5159 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2230 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_1929 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) (shared_expr_Classification082_54 c2_node c2_sign c3_node c3_sign) (shared_expr_Classification082_50 c2_node c2_sign c3_node c3_sign) (shared_expr_Classification082_42 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ((shared_expr_Classification082_45 c2_depth c2_node c3_depth c3_node c3_sign) ∨ (shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node)))
  have n0 : (shared_expr_Classification082_57 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7307 c2_depth c3_depth) (replay_5118 c2_depth c3_depth)
  have n1 : ((shared_expr_Classification082_54 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Classification082_50 c2_node c2_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_7333 c2_node c2_sign c3_node c3_sign) (replay_5131 c2_node c2_sign c3_node c3_sign)
  have n2 : (shared_expr_Classification082_47 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := by
    exact Iff.mp (normalization_7393 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (replay_5158 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_7395 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) hn

theorem normalized_1930 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_58 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ ((shared_expr_Classification082_45 c2_depth c2_node c3_depth c3_node c3_sign) ∨ (shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node)))
abbrev shared_expr_Classification082_59 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_58 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ∨ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification082_50 c2_node c2_sign c3_node c3_sign)))
theorem normalization_7396 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7303 c2_depth c3_depth) (normalization_7391 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) (and_congr (not_congr (normalization_7303 c2_depth c3_depth)) (normalization_7331 c2_node c2_sign c3_node c3_sign)))

theorem normalization_7397 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2230 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ ((shared_expr_Classification082_52 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (iff_congr (normalization_7394 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (normalization_7396 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5160 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2230 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_1930 ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) (shared_expr_Classification082_50 c2_node c2_sign c3_node c3_sign) ((shared_expr_Classification082_45 c2_depth c2_node c3_depth c3_node c3_sign) ∨ (shared_expr_Classification082_39 c2_depth c2_node c2_sign c3_depth c3_node)))
  have hn := ht
  exact Iff.mpr (normalization_7397 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) hn

theorem normalized_1931 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7398 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ ((shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (iff_congr (normalization_7256 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (normalization_7396 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5161 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : ((formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
  classical
  have ht := (normalized_1931 (shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (shared_expr_Classification082_52 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
  have n0 : ((shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_52 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_7395 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (replay_5159 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)
  have n1 : ((shared_expr_Classification082_52 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_7397 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (replay_5160 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7398 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) hn

abbrev shared_expr_Classification082_60 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (c3_kind = (2 : Int))) ∧ (formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) ∧ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev formula_2231 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_60 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_1932 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∧ p2) ↔ (p1 ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7399 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) ∧ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (and_congr (normalization_6838 c3_kind) (normalization_7396 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

abbrev shared_expr_Classification082_61 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
theorem normalization_7400 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2231 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_61 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7257 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7399 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5162 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2231 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_1932 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) (shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
  have n0 : ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_7290 c3_kind) (replay_5111 c3_kind)
  have n1 : ((shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := by
    exact Iff.mp (normalization_7398 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) (replay_5161 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7400 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Classification082_62 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) ∧ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev formula_2232 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_62 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_1933 (p0 p1 : Prop) : ((p0 ∧ p1) ↔ (¬ ((¬ p0) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7401 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (¬ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (not_congr (normalization_7396 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

theorem normalization_7402 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))) ↔ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))) := (or_congr (normalization_6839 c3_kind) (normalization_7401 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

theorem normalization_7403 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))) := (not_congr (normalization_7402 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

abbrev shared_expr_Classification082_63 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
theorem normalization_7404 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2232 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_63 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7399 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7403 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5163 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2232 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_1933 ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7404 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Classification082_64 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (c3_kind = (2 : Int))) ∧ (formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev formula_2233 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_64 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_1934 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_65 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
theorem normalization_7405 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2233 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_65 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7257 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7403 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5164 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2233 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_1934 ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) (((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))))
  have n0 : (shared_expr_Classification082_61 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7400 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5162 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have n1 : (shared_expr_Classification082_63 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7404 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5163 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7405 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Classification082_66 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ∧ (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev shared_expr_Classification082_67 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) ∨ (shared_expr_Classification082_66 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
abbrev formula_2234 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_67 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Classification082_68 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))) ↔ (formula_2234 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
abbrev formula_2235 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_68 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_1935 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_69 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) ∧ (¬ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev shared_expr_Classification082_70 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) ∨ (shared_expr_Classification082_69 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7406 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2234 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_70 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_992 c2_kind) (normalization_7284 c3_kind)) (and_congr (not_congr (normalization_992 c2_kind)) (normalization_7403 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Classification082_71 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev shared_expr_Classification082_72 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) ∨ (shared_expr_Classification082_71 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
abbrev shared_expr_Classification082_73 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_70 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7407 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2235 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_73 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7258 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7406 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5165 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2235 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_1935 (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification082_56 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))))
  have n0 : ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1083 c2_kind) (replay_506 c2_kind)
  have n1 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_7286 c3_kind) (replay_5108 c3_kind)
  have n2 : (shared_expr_Classification082_65 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7405 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5164 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_7407 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

theorem normalized_1936 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_74 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (¬ ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev shared_expr_Classification082_75 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_74 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ∨ ((¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))))
theorem normalization_7408 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_991 c2_kind) (normalization_7403 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) (and_congr (not_congr (normalization_991 c2_kind)) (normalization_7284 c3_kind)))

abbrev shared_expr_Classification082_76 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_70 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7409 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : ((formula_2234 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ (shared_expr_Classification082_76 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7406 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7408 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5166 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : ((formula_2234 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := by
  classical
  have ht := (normalized_1936 ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) ((¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification082_59 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))))
  have hn := ht
  exact Iff.mpr (normalization_7409 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Classification082_77 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))) ↔ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
abbrev formula_2236 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_77 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_1937 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_78 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7410 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2236 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_78 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7258 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7408 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5167 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2236 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_1937 (shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (shared_expr_Classification082_70 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
  have n0 : (shared_expr_Classification082_73 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7407 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5165 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have n1 : (shared_expr_Classification082_76 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7409 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5166 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7410 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Classification082_79 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((formula_2206 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ∧ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev formula_2237 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_79 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_1938 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∧ p2) ↔ (p1 ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7411 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ∧ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := (and_congr (normalization_6745 c3_kind) (normalization_7408 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

abbrev shared_expr_Classification082_80 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_7412 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2237 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_80 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7259 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7411 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5168 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2237 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_1938 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
  have n0 : ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_7265 c3_kind) (replay_5101 c3_kind)
  have n1 : (shared_expr_Classification082_78 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7410 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5167 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7412 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Classification082_81 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ∧ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev formula_2238 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_81 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_1939 (p0 p1 : Prop) : ((p0 ∧ p1) ↔ (¬ ((¬ p0) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7413 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := (not_congr (normalization_7408 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

theorem normalization_7414 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))) ↔ ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))) := (or_congr (normalization_6746 c3_kind) (normalization_7413 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

theorem normalization_7415 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))) := (not_congr (normalization_7414 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

abbrev shared_expr_Classification082_82 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
theorem normalization_7416 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2238 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_82 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7411 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7415 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5169 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2238 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_1939 ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7416 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Classification082_83 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((formula_2206 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev formula_2239 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_83 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem normalized_1940 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_84 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ (¬ ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
theorem normalization_7417 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2239 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification082_84 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (iff_congr (normalization_7259 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (normalization_7415 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5170 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2239 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  classical
  have ht := (normalized_1940 ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))))
  have n0 : (shared_expr_Classification082_80 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7412 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5168 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have n1 : (shared_expr_Classification082_82 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7416 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5169 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7417 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) hn

abbrev shared_expr_Classification082_85 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) ∧ (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev shared_expr_Classification082_86 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∧ (formula_2184 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ∨ (shared_expr_Classification082_85 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
abbrev formula_2240 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_86 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Classification082_87 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2207 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2240 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2241 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_87 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1941 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_88 (c2_group c2_mode c3_group c3_mode : Int) : Prop := ((((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification082_89 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification082_88 c2_group c2_mode c3_group c3_mode)))
abbrev shared_expr_Classification082_90 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification082_89 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
abbrev shared_expr_Classification082_91 (c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∧ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification082_90 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
abbrev shared_expr_Classification082_92 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) ∧ (¬ ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev shared_expr_Classification082_93 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_91 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Classification082_92 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7418 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2240 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification082_93 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (or_congr (and_congr (normalization_890 c2_kind) (normalization_7278 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) (and_congr (not_congr (normalization_890 c2_kind)) (normalization_7415 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Classification082_94 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (((((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification082_95 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification082_94 c2_group c2_mode c3_group c3_mode)) ∨ ((¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification082_96 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification082_95 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
abbrev shared_expr_Classification082_97 (c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification082_96 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
abbrev shared_expr_Classification082_98 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev shared_expr_Classification082_99 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_97 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Classification082_98 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
abbrev shared_expr_Classification082_100 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_99 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification082_93 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
theorem normalization_7419 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2241 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification082_100 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_7260 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_7418 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification082_101 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification082_96 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification082_90 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem replay_5171 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2241 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1941 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification082_96 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification082_90 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification082_72 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))))
  have n0 : ((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_892 c2_kind) (replay_468 c2_kind)
  have n1 : (shared_expr_Classification082_101 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_7280 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (replay_5105 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)
  have n2 : (shared_expr_Classification082_84 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
    exact Iff.mp (normalization_7417 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (replay_5170 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_7419 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

abbrev shared_expr_Classification082_102 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2240 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2185 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2242 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_102 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1942 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_103 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (¬ ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev shared_expr_Classification082_104 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_103 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ∨ (shared_expr_Classification082_91 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode))
theorem normalization_7420 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2185 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification082_104 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (or_congr (and_congr (normalization_889 c2_kind) (normalization_7415 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) (and_congr (not_congr (normalization_889 c2_kind)) (normalization_7278 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)))

abbrev shared_expr_Classification082_105 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_93 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification082_104 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
theorem normalization_7421 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2242 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification082_105 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_7418 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_7420 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5172 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2242 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1942 ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification082_90 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification082_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))))
  have hn := ht
  exact Iff.mpr (normalization_7421 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

abbrev shared_expr_Classification082_106 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2207 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2185 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2243 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_106 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1943 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification082_107 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification082_99 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification082_104 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
theorem normalization_7422 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2243 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification082_107 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_7260 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_7420 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5173 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2243 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1943 (shared_expr_Classification082_99 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (shared_expr_Classification082_93 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (shared_expr_Classification082_104 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
  have n0 : (shared_expr_Classification082_100 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
    exact Iff.mp (normalization_7419 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_5171 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)
  have n1 : (shared_expr_Classification082_105 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
    exact Iff.mp (normalization_7421 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_5172 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7422 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

-- Checked replay of mp.
theorem replay_5174 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2185 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_5173 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_5098 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i290)

abbrev shared_expr_Classification082_108 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev formula_2244 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification082_108 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

-- Checked replay of unit-resolution.
theorem replay_5175 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2244 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  exact (Or.elim (replay_5092 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (fun l0 => (Or.inl l0)) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_5174 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i290)))))))

-- Checked replay of unit-resolution.
theorem replay_5176 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) (i236 : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) : (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))) := by
  exact (Or.elim (replay_5175 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i290) (fun l0 => (False.elim (l0 i236))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5177 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) (i236 : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) : ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) := by
  exact (Or.elim (replay_5091 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) (fun l0 => (False.elim ((replay_5176 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i290 i236) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_5178 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i236 : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) : (¬ (formula_2035 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) := by
  exact (Or.elim (replay_5008 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5177 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i290 i236)))) (fun t1 => (False.elim ((replay_5090 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i284 i10 i287 i11) t1))))))

-- Checked replay of unit-resolution.
theorem replay_5179 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) (i277 : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i236 : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) := by
  exact (Or.elim (replay_5007 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i277) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_5178 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i284 i10 i290 i287 i11 i236) t0))))

-- Checked replay of unit-resolution.
theorem replay_5180 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) (i180 : ((formula_1693 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) (i277 : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i236 : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) : (formula_1656 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := by
  exact (Or.elim (replay_2756 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i180) (fun l0 => (False.elim (l0 (replay_5179 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i284 i10 i290 i277 i287 i11 i236)))) (fun t0 => t0))

theorem propositional_1944 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5181 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ∨ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (propositional_1944 (r2_mode ≤ (4 : Int)) (r2_mode ≥ (4 : Int)) (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

abbrev shared_expr_Classification082_109 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) ∨ (¬ ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))))
abbrev formula_2245 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification082_109 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)

theorem propositional_1945 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5182 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_2245 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) := by
  exact (propositional_1945 ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level))) ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level))) ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level))))

theorem propositional_1946 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5183 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ∨ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (propositional_1946 (r2_mode ≤ (2 : Int)) (r2_mode ≥ (2 : Int)) (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

theorem propositional_1947 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5184 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : ((¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level))) := by
  exact (propositional_1947 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))

theorem propositional_1948 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))) ∨ ((¬ p0) ∧ (¬ p7)))) ∨ p0 ∨ (¬ p7)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5185 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : ((¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ (formula_1170 c2_depth c2_kind c2_sign r2_level))) := by
  exact (propositional_1948 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((c2_node % (2 : Int)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) (formula_1170 c2_depth c2_kind c2_sign r2_level))

-- Checked replay of unit-resolution.
theorem replay_5186 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) : (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5185 c2_depth c2_kind c2_node c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i291 l1))) (fun t1 => (False.elim (t1 i292))))))

-- Checked replay of unit-resolution.
theorem replay_5187 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) : ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5183 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5186 c2_depth c2_kind c2_node c2_sign r2_group r2_level i291 i292) t0))))

theorem propositional_1949 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5188 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level))) ∨ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (propositional_1949 (r2_mode ≤ (0 : Int)) (r2_mode ≥ (0 : Int)) (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level))

theorem propositional_1950 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6))))) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ p0) ∧ (¬ p9)))) ∨ p0 ∨ (¬ p9)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5189 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : ((¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) := by
  exact (propositional_1950 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_5190 (c2_depth c2_kind c2_sign r2_group r2_level : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) : (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5189 c2_depth c2_kind c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i291 l1))) (fun t1 => (False.elim (t1 i231))))))

-- Checked replay of unit-resolution.
theorem replay_5191 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) : ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5188 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5190 c2_depth c2_kind c2_sign r2_group r2_level i291 i231) t0))))

theorem propositional_1951 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5192 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level))) ∨ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (propositional_1951 (r2_mode ≤ (1 : Int)) (r2_mode ≥ (1 : Int)) (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level))

end H4Formal.Generated.Classification
