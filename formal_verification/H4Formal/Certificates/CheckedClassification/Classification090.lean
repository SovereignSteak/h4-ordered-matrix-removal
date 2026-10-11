import H4Formal.Certificates.CheckedClassification.Classification089

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_5812 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i384 : (formula_2346 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2361 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_5811 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_5810 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i384)

abbrev shared_expr_Classification090_0 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : Prop := ((((c1_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2354 c1_group c1_level c1_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c1_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c1_mode ≥ (4 : Int))))
abbrev shared_expr_Classification090_1 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : Prop := ((((c1_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2337 c1_group c1_level c1_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c1_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c1_mode ≥ (4 : Int))))
abbrev formula_2363 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : Prop := ((shared_expr_Classification090_0 c1_group c1_level c1_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification090_1 c1_group c1_level c1_mode c3_group c3_level c3_mode))

theorem normalized_2108 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7519 (c1_level c3_level : Int) : ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_7520 (c1_level c3_level : Int) : (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) := (not_congr (normalization_7519 c1_level c3_level))

theorem normalization_7521 (c1_level c3_level : Int) : ((¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ ((¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) := (or_congr (normalization_7520 c1_level c3_level) (normalization_7493 c1_level c3_level))

theorem normalization_7522 (c1_mode c3_mode : Int) : ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ↔ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_7523 (c1_mode c3_mode : Int) : (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) := (not_congr (normalization_7522 c1_mode c3_mode))

theorem normalization_7524 (c1_mode c3_mode : Int) : ((¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_7523 c1_mode c3_mode) (normalization_7490 c1_mode c3_mode))

abbrev shared_expr_Classification090_2 (c1_group c1_mode c3_group c3_mode : Int) : Prop := ((((¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c1_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))))
theorem normalization_7525 (c1_group c1_mode c3_group c3_mode : Int) : (formula_2336 c1_group c1_mode c3_group c3_mode) ↔ (shared_expr_Classification090_2 c1_group c1_mode c3_group c3_mode) := (or_congr (and_congr (normalization_7524 c1_mode c3_mode) (normalization_7490 c1_mode c3_mode)) (and_congr (not_congr (normalization_7524 c1_mode c3_mode)) (normalization_7488 c1_group c3_group)))

abbrev shared_expr_Classification090_3 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification090_2 c1_group c1_mode c3_group c3_mode)))
theorem normalization_7526 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : (formula_2337 c1_group c1_level c1_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification090_3 c1_group c1_level c1_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7521 c1_level c3_level) (normalization_7493 c1_level c3_level)) (and_congr (not_congr (normalization_7521 c1_level c3_level)) (normalization_7525 c1_group c1_mode c3_group c3_mode)))

abbrev shared_expr_Classification090_4 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification090_3 c1_group c1_level c1_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c1_mode) ≤ (3 : Int)))))
theorem normalization_7527 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : (shared_expr_Classification090_1 c1_group c1_level c1_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7453 c1_mode c3_mode) (normalization_7526 c1_group c1_level c1_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_7453 c1_mode c3_mode)) (normalization_1824 c1_mode)))

abbrev shared_expr_Classification090_5 (c1_group c1_mode c3_group c3_mode : Int) : Prop := (((((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c1_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification090_6 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : Prop := (((((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification090_5 c1_group c1_mode c3_group c3_mode)) ∨ ((¬ (((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification090_7 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification090_6 c1_group c1_level c1_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c1_mode) ≤ (3 : Int)))))
theorem normalization_7528 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : (formula_2363 c1_group c1_level c1_mode c3_group c3_level c3_mode) ↔ ((shared_expr_Classification090_7 c1_group c1_level c1_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)) := (iff_congr (normalization_7495 c1_group c1_level c1_mode c3_group c3_level c3_mode) (normalization_7527 c1_group c1_level c1_mode c3_group c3_level c3_mode))

-- Checked replay of rewrite.
theorem replay_5813 (c1_group c1_level c1_mode c3_group c3_level c3_mode : Int) : (formula_2363 c1_group c1_level c1_mode c3_group c3_level c3_mode) := by
  classical
  have ht := (normalized_2108 ((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ((c1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ((c1_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ((c1_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)) ((c1_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)) ((c1_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7528 c1_group c1_level c1_mode c3_group c3_level c3_mode) hn

abbrev formula_2364 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ∨ (shared_expr_Classification090_1 c1_group c1_level c1_mode c3_group c3_level c3_mode))

theorem normalized_2109 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7529 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2364 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6745 c3_kind) (normalization_7527 c1_group c1_level c1_mode c3_group c3_level c3_mode))

abbrev shared_expr_Classification090_8 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_7 c1_group c1_level c1_mode c3_group c3_level c3_mode)) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)))
theorem normalization_7530 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2355 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2364 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification090_8 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_7496 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) (normalization_7529 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of monotonicity.
theorem replay_5814 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2355 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2364 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2109 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification090_7 c1_group c1_level c1_mode c3_group c3_level c3_mode) (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode))
  have n0 : ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_7265 c3_kind) (replay_5101 c3_kind)
  have n1 : ((shared_expr_Classification090_7 c1_group c1_level c1_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)) := by
    exact Iff.mp (normalization_7528 c1_group c1_level c1_mode c3_group c3_level c3_mode) (replay_5813 c1_group c1_level c1_mode c3_group c3_level c3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7530 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2110 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7531 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2338 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6743 c3_kind) (or_congr (normalization_6744 c3_kind) (normalization_7527 c1_group c1_level c1_mode c3_group c3_level c3_mode)))

abbrev shared_expr_Classification090_9 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)))
theorem normalization_7532 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2364 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2338 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification090_9 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_7529 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) (normalization_7531 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of rewrite.
theorem replay_5815 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2364 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2338 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2110 ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)) (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode))
  have hn := ht
  exact Iff.mpr (normalization_7532 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2111 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_10 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_7 c1_group c1_level c1_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)))
theorem normalization_7533 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2355 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2338 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification090_10 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_7496 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) (normalization_7531 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of trans.
theorem replay_5816 (c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2355 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2338 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2111 ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_7 c1_group c1_level c1_mode c3_group c3_level c3_mode)) (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification090_4 c1_group c1_level c1_mode c3_group c3_level c3_mode)))
  have n0 : (shared_expr_Classification090_8 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_7530 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) (replay_5814 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode)
  have n1 : (shared_expr_Classification090_9 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_7532 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) (replay_5815 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7533 c1_group c1_level c1_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2112 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7534 (c1_depth c3_depth : Int) : (c1_depth ≤ c3_depth) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_7535 (c1_depth c3_depth : Int) : (c1_depth ≥ c3_depth) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7536 (c1_depth c3_depth : Int) : ((c1_depth ≤ c3_depth) ∧ (c1_depth ≥ c3_depth)) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_7534 c1_depth c3_depth) (normalization_7535 c1_depth c3_depth))

abbrev shared_expr_Classification090_11 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
theorem normalization_7537 (c1_depth c3_depth : Int) : ((c1_depth = c3_depth) ↔ ((c1_depth ≤ c3_depth) ∧ (c1_depth ≥ c3_depth))) ↔ (shared_expr_Classification090_11 c1_depth c3_depth) := (iff_congr (normalization_7433 c1_depth c3_depth) (normalization_7536 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5817 (c1_depth c3_depth : Int) : ((c1_depth = c3_depth) ↔ ((c1_depth ≤ c3_depth) ∧ (c1_depth ≥ c3_depth))) := by
  classical
  have ht := (normalized_2112 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7537 c1_depth c3_depth) hn

theorem normalized_2113 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7538 (c1_depth c3_depth : Int) : ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_7539 (c1_depth c3_depth : Int) : ((c1_depth ≤ c3_depth) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := (iff_congr (normalization_7534 c1_depth c3_depth) (normalization_7538 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5818 (c1_depth c3_depth : Int) : ((c1_depth ≤ c3_depth) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2113 ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7539 c1_depth c3_depth) hn

theorem normalized_2114 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7540 (c1_depth c3_depth : Int) : ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7541 (c1_depth c3_depth : Int) : ((c1_depth ≥ c3_depth) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_7535 c1_depth c3_depth) (normalization_7540 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5819 (c1_depth c3_depth : Int) : ((c1_depth ≥ c3_depth) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2114 ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7541 c1_depth c3_depth) hn

theorem normalized_2115 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7542 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_7538 c1_depth c3_depth) (normalization_7540 c1_depth c3_depth))

theorem normalization_7543 (c1_depth c3_depth : Int) : (((c1_depth ≤ c3_depth) ∧ (c1_depth ≥ c3_depth)) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification090_11 c1_depth c3_depth) := (iff_congr (normalization_7536 c1_depth c3_depth) (normalization_7542 c1_depth c3_depth))

-- Checked replay of monotonicity.
theorem replay_5820 (c1_depth c3_depth : Int) : (((c1_depth ≤ c3_depth) ∧ (c1_depth ≥ c3_depth)) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2115 ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
  have n0 : (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_7539 c1_depth c3_depth) (replay_5818 c1_depth c3_depth)
  have n1 : ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_7541 c1_depth c3_depth) (replay_5819 c1_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7543 c1_depth c3_depth) hn

abbrev shared_expr_Classification090_12 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))))
abbrev formula_2365 (c1_depth c3_depth : Int) : Prop := (shared_expr_Classification090_12 c1_depth c3_depth)

theorem normalized_2116 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7544 (c1_depth c3_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := (not_congr (normalization_7538 c1_depth c3_depth))

theorem normalization_7545 (c1_depth c3_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_7540 c1_depth c3_depth))

theorem normalization_7546 (c1_depth c3_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_7544 c1_depth c3_depth) (normalization_7545 c1_depth c3_depth))

theorem normalization_7547 (c1_depth c3_depth : Int) : (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_7546 c1_depth c3_depth))

abbrev shared_expr_Classification090_13 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))))
theorem normalization_7548 (c1_depth c3_depth : Int) : (formula_2365 c1_depth c3_depth) ↔ (shared_expr_Classification090_13 c1_depth c3_depth) := (iff_congr (normalization_7542 c1_depth c3_depth) (normalization_7547 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5821 (c1_depth c3_depth : Int) : (formula_2365 c1_depth c3_depth) := by
  classical
  have ht := (normalized_2116 ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7548 c1_depth c3_depth) hn

theorem normalized_2117 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7549 (c1_depth c3_depth : Int) : (((c1_depth ≤ c3_depth) ∧ (c1_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification090_13 c1_depth c3_depth) := (iff_congr (normalization_7536 c1_depth c3_depth) (normalization_7547 c1_depth c3_depth))

-- Checked replay of trans.
theorem replay_5822 (c1_depth c3_depth : Int) : (((c1_depth ≤ c3_depth) ∧ (c1_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2117 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Classification090_13 c1_depth c3_depth))
  have n0 : (shared_expr_Classification090_11 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7543 c1_depth c3_depth) (replay_5820 c1_depth c3_depth)
  have n1 : (shared_expr_Classification090_13 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7548 c1_depth c3_depth) (replay_5821 c1_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7549 c1_depth c3_depth) hn

theorem normalized_2118 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7550 (c1_depth c3_depth : Int) : ((c1_depth = c3_depth) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification090_13 c1_depth c3_depth) := (iff_congr (normalization_7433 c1_depth c3_depth) (normalization_7547 c1_depth c3_depth))

-- Checked replay of trans.
theorem replay_5823 (c1_depth c3_depth : Int) : ((c1_depth = c3_depth) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2118 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Classification090_13 c1_depth c3_depth))
  have n0 : (shared_expr_Classification090_11 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7537 c1_depth c3_depth) (replay_5817 c1_depth c3_depth)
  have n1 : (shared_expr_Classification090_13 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7549 c1_depth c3_depth) (replay_5822 c1_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7550 c1_depth c3_depth) hn

theorem normalized_2119 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7551 (c1_node c3_node : Int) : (c1_node ≤ c3_node) ↔ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7552 (c1_node c3_node : Int) : (c1_node ≥ c3_node) ↔ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7553 (c1_node c3_node : Int) : ((c1_node ≤ c3_node) ∧ (c1_node ≥ c3_node)) ↔ (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_7551 c1_node c3_node) (normalization_7552 c1_node c3_node))

abbrev shared_expr_Classification090_14 (c1_node c3_node : Int) : Prop := ((((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_7554 (c1_node c3_node : Int) : ((c1_node = c3_node) ↔ ((c1_node ≤ c3_node) ∧ (c1_node ≥ c3_node))) ↔ (shared_expr_Classification090_14 c1_node c3_node) := (iff_congr (normalization_7434 c1_node c3_node) (normalization_7553 c1_node c3_node))

-- Checked replay of rewrite.
theorem replay_5824 (c1_node c3_node : Int) : ((c1_node = c3_node) ↔ ((c1_node ≤ c3_node) ∧ (c1_node ≥ c3_node))) := by
  classical
  have ht := (normalized_2119 (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7554 c1_node c3_node) hn

theorem normalized_2120 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7555 (c1_node c3_node : Int) : ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7556 (c1_node c3_node : Int) : ((c1_node ≤ c3_node) ↔ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (iff_congr (normalization_7551 c1_node c3_node) (normalization_7555 c1_node c3_node))

-- Checked replay of rewrite.
theorem replay_5825 (c1_node c3_node : Int) : ((c1_node ≤ c3_node) ↔ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2120 ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7556 c1_node c3_node) hn

theorem normalized_2121 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7557 (c1_node c3_node : Int) : ((c1_node ≥ c3_node) ↔ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_7552 c1_node c3_node) (normalization_7497 c1_node c3_node))

-- Checked replay of rewrite.
theorem replay_5826 (c1_node c3_node : Int) : ((c1_node ≥ c3_node) ↔ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2121 ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7557 c1_node c3_node) hn

theorem normalized_2122 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7558 (c1_node c3_node : Int) : (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_7555 c1_node c3_node) (normalization_7497 c1_node c3_node))

theorem normalization_7559 (c1_node c3_node : Int) : (((c1_node ≤ c3_node) ∧ (c1_node ≥ c3_node)) ↔ (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification090_14 c1_node c3_node) := (iff_congr (normalization_7553 c1_node c3_node) (normalization_7558 c1_node c3_node))

-- Checked replay of monotonicity.
theorem replay_5827 (c1_node c3_node : Int) : (((c1_node ≤ c3_node) ∧ (c1_node ≥ c3_node)) ↔ (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2122 ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have n0 : (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_7556 c1_node c3_node) (replay_5825 c1_node c3_node)
  have n1 : ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_7557 c1_node c3_node) (replay_5826 c1_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7559 c1_node c3_node) hn

abbrev shared_expr_Classification090_15 (c1_node c3_node : Int) : Prop := ((((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))))
abbrev formula_2366 (c1_node c3_node : Int) : Prop := (shared_expr_Classification090_15 c1_node c3_node)

theorem normalized_2123 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7560 (c1_node c3_node : Int) : (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_7555 c1_node c3_node))

theorem normalization_7561 (c1_node c3_node : Int) : ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_7560 c1_node c3_node) (normalization_7498 c1_node c3_node))

theorem normalization_7562 (c1_node c3_node : Int) : (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_7561 c1_node c3_node))

abbrev shared_expr_Classification090_16 (c1_node c3_node : Int) : Prop := ((((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))))
theorem normalization_7563 (c1_node c3_node : Int) : (formula_2366 c1_node c3_node) ↔ (shared_expr_Classification090_16 c1_node c3_node) := (iff_congr (normalization_7558 c1_node c3_node) (normalization_7562 c1_node c3_node))

-- Checked replay of rewrite.
theorem replay_5828 (c1_node c3_node : Int) : (formula_2366 c1_node c3_node) := by
  classical
  have ht := (normalized_2123 ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7563 c1_node c3_node) hn

theorem normalized_2124 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7564 (c1_node c3_node : Int) : (((c1_node ≤ c3_node) ∧ (c1_node ≥ c3_node)) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification090_16 c1_node c3_node) := (iff_congr (normalization_7553 c1_node c3_node) (normalization_7562 c1_node c3_node))

-- Checked replay of trans.
theorem replay_5829 (c1_node c3_node : Int) : (((c1_node ≤ c3_node) ∧ (c1_node ≥ c3_node)) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2124 (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Classification090_16 c1_node c3_node))
  have n0 : (shared_expr_Classification090_14 c1_node c3_node) := by
    exact Iff.mp (normalization_7559 c1_node c3_node) (replay_5827 c1_node c3_node)
  have n1 : (shared_expr_Classification090_16 c1_node c3_node) := by
    exact Iff.mp (normalization_7563 c1_node c3_node) (replay_5828 c1_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7564 c1_node c3_node) hn

theorem normalized_2125 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7565 (c1_node c3_node : Int) : ((c1_node = c3_node) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification090_16 c1_node c3_node) := (iff_congr (normalization_7434 c1_node c3_node) (normalization_7562 c1_node c3_node))

-- Checked replay of trans.
theorem replay_5830 (c1_node c3_node : Int) : ((c1_node = c3_node) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2125 (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Classification090_16 c1_node c3_node))
  have n0 : (shared_expr_Classification090_14 c1_node c3_node) := by
    exact Iff.mp (normalization_7554 c1_node c3_node) (replay_5824 c1_node c3_node)
  have n1 : (shared_expr_Classification090_16 c1_node c3_node) := by
    exact Iff.mp (normalization_7564 c1_node c3_node) (replay_5829 c1_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7565 c1_node c3_node) hn

theorem normalized_2126 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7566 (c1_sign c3_sign : Int) : ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (and_congr (normalization_1600 c1_sign) (normalization_6849 c3_sign))

abbrev shared_expr_Classification090_17 (c1_sign c3_sign : Int) : Prop := (((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))))
theorem normalization_7567 (c1_sign c3_sign : Int) : (((c1_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) ↔ (shared_expr_Classification090_17 c1_sign c3_sign) := (iff_congr (normalization_7435 c1_sign c3_sign) (normalization_7566 c1_sign c3_sign))

-- Checked replay of monotonicity.
theorem replay_5831 (c1_sign c3_sign : Int) : (((c1_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_2126 (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1698 c1_sign) (replay_636 c1_sign)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6942 c3_sign) (replay_4980 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7567 c1_sign c3_sign) hn

abbrev shared_expr_Classification090_18 (c1_sign c3_sign : Int) : Prop := (((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev formula_2367 (c1_sign c3_sign : Int) : Prop := (shared_expr_Classification090_18 c1_sign c3_sign)

theorem normalized_2127 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7568 (c1_sign c3_sign : Int) : ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ↔ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) := (or_congr (normalization_1596 c1_sign) (or_congr (normalization_1598 c1_sign) (or_congr (normalization_6845 c3_sign) (normalization_6847 c3_sign))))

theorem normalization_7569 (c1_sign c3_sign : Int) : (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_7568 c1_sign c3_sign))

abbrev shared_expr_Classification090_19 (c1_sign c3_sign : Int) : Prop := (((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_7570 (c1_sign c3_sign : Int) : (formula_2367 c1_sign c3_sign) ↔ (shared_expr_Classification090_19 c1_sign c3_sign) := (iff_congr (normalization_7566 c1_sign c3_sign) (normalization_7569 c1_sign c3_sign))

-- Checked replay of rewrite.
theorem replay_5832 (c1_sign c3_sign : Int) : (formula_2367 c1_sign c3_sign) := by
  classical
  have ht := (normalized_2127 ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7570 c1_sign c3_sign) hn

theorem normalized_2128 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_20 (c1_sign c3_sign : Int) : Prop := (((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_7571 (c1_sign c3_sign : Int) : (((c1_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (shared_expr_Classification090_20 c1_sign c3_sign) := (iff_congr (normalization_7435 c1_sign c3_sign) (normalization_7569 c1_sign c3_sign))

-- Checked replay of trans.
theorem replay_5833 (c1_sign c3_sign : Int) : (((c1_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2128 ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification090_17 c1_sign c3_sign) := by
    exact Iff.mp (normalization_7567 c1_sign c3_sign) (replay_5831 c1_sign c3_sign)
  have n1 : (shared_expr_Classification090_19 c1_sign c3_sign) := by
    exact Iff.mp (normalization_7570 c1_sign c3_sign) (replay_5832 c1_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7571 c1_sign c3_sign) hn

abbrev shared_expr_Classification090_21 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification090_22 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification090_21 c1_node c1_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))
abbrev formula_2368 (c1_node c1_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification090_22 c1_node c1_sign c3_node c3_sign)

abbrev shared_expr_Classification090_23 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((((c1_node = c3_node) ∧ ((c1_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c1_node = c3_node)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_2368 c1_node c1_sign c3_node c3_sign))
abbrev formula_2369 (c1_node c1_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification090_23 c1_node c1_sign c3_node c3_sign)

theorem normalized_2129 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_24 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification090_25 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification090_24 c1_node c1_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_7572 (c1_node c1_sign c3_node c3_sign : Int) : (formula_2368 c1_node c1_sign c3_node c3_sign) ↔ (shared_expr_Classification090_25 c1_node c1_sign c3_node c3_sign) := (or_congr (and_congr (normalization_7562 c1_node c3_node) (normalization_7569 c1_sign c3_sign)) (and_congr (not_congr (normalization_7562 c1_node c3_node)) (normalization_7498 c1_node c3_node)))

abbrev shared_expr_Classification090_26 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification090_27 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification090_26 c1_node c1_sign c3_node c3_sign) ∨ ((¬ (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_7573 (c1_node c1_sign c3_node c3_sign : Int) : (formula_2369 c1_node c1_sign c3_node c3_sign) ↔ ((shared_expr_Classification090_27 c1_node c1_sign c3_node c3_sign) ↔ (shared_expr_Classification090_25 c1_node c1_sign c3_node c3_sign)) := (iff_congr (normalization_7499 c1_node c1_sign c3_node c3_sign) (normalization_7572 c1_node c1_sign c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5834 (c1_node c1_sign c3_node c3_sign : Int) : (formula_2369 c1_node c1_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_2129 (((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification090_16 c1_node c3_node) := by
    exact Iff.mp (normalization_7565 c1_node c3_node) (replay_5830 c1_node c3_node)
  have n1 : (shared_expr_Classification090_20 c1_sign c3_sign) := by
    exact Iff.mp (normalization_7571 c1_sign c3_sign) (replay_5833 c1_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7573 c1_node c1_sign c3_node c3_sign) hn

theorem normalized_2130 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_28 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_24 c1_node c1_sign c3_node c3_sign))
theorem normalization_7574 (c1_node c1_sign c3_node c3_sign : Int) : (formula_2332 c1_node c1_sign c3_node c3_sign) ↔ (shared_expr_Classification090_28 c1_node c1_sign c3_node c3_sign) := (or_congr (and_congr (normalization_7561 c1_node c3_node) (normalization_7498 c1_node c3_node)) (and_congr (not_congr (normalization_7561 c1_node c3_node)) (normalization_7569 c1_sign c3_sign)))

theorem normalization_7575 (c1_node c1_sign c3_node c3_sign : Int) : ((formula_2368 c1_node c1_sign c3_node c3_sign) ↔ (formula_2332 c1_node c1_sign c3_node c3_sign)) ↔ ((shared_expr_Classification090_25 c1_node c1_sign c3_node c3_sign) ↔ (shared_expr_Classification090_28 c1_node c1_sign c3_node c3_sign)) := (iff_congr (normalization_7572 c1_node c1_sign c3_node c3_sign) (normalization_7574 c1_node c1_sign c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5835 (c1_node c1_sign c3_node c3_sign : Int) : ((formula_2368 c1_node c1_sign c3_node c3_sign) ↔ (formula_2332 c1_node c1_sign c3_node c3_sign)) := by
  classical
  have ht := (normalized_2130 ((¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c1_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7575 c1_node c1_sign c3_node c3_sign) hn

abbrev shared_expr_Classification090_29 (c1_node c1_sign c3_node c3_sign : Int) : Prop := ((((c1_node = c3_node) ∧ ((c1_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c1_node = c3_node)) ∧ (¬ ((c1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_2332 c1_node c1_sign c3_node c3_sign))
abbrev formula_2370 (c1_node c1_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification090_29 c1_node c1_sign c3_node c3_sign)

theorem normalized_2131 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7576 (c1_node c1_sign c3_node c3_sign : Int) : (formula_2370 c1_node c1_sign c3_node c3_sign) ↔ ((shared_expr_Classification090_27 c1_node c1_sign c3_node c3_sign) ↔ (shared_expr_Classification090_28 c1_node c1_sign c3_node c3_sign)) := (iff_congr (normalization_7499 c1_node c1_sign c3_node c3_sign) (normalization_7574 c1_node c1_sign c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5836 (c1_node c1_sign c3_node c3_sign : Int) : (formula_2370 c1_node c1_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_2131 (shared_expr_Classification090_27 c1_node c1_sign c3_node c3_sign) (shared_expr_Classification090_25 c1_node c1_sign c3_node c3_sign) (shared_expr_Classification090_28 c1_node c1_sign c3_node c3_sign))
  have n0 : ((shared_expr_Classification090_27 c1_node c1_sign c3_node c3_sign) ↔ (shared_expr_Classification090_25 c1_node c1_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_7573 c1_node c1_sign c3_node c3_sign) (replay_5834 c1_node c1_sign c3_node c3_sign)
  have n1 : ((shared_expr_Classification090_25 c1_node c1_sign c3_node c3_sign) ↔ (shared_expr_Classification090_28 c1_node c1_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_7575 c1_node c1_sign c3_node c3_sign) (replay_5835 c1_node c1_sign c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7576 c1_node c1_sign c3_node c3_sign) hn

theorem normalized_2132 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7577 (c1_depth c3_depth : Int) : ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_7578 (c1_depth c3_depth : Int) : ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_7579 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_7577 c1_depth c3_depth) (normalization_7578 c1_depth c3_depth))

abbrev shared_expr_Classification090_30 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
theorem normalization_7580 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Classification090_30 c1_depth c3_depth) := (iff_congr (normalization_7500 c1_depth c3_depth) (normalization_7579 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5837 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_2132 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7580 c1_depth c3_depth) hn

abbrev shared_expr_Classification090_31 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))))
abbrev formula_2371 (c1_depth c3_depth : Int) : Prop := (shared_expr_Classification090_31 c1_depth c3_depth)

theorem normalized_2133 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7581 (c1_depth c3_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := (not_congr (normalization_7577 c1_depth c3_depth))

theorem normalization_7582 (c1_depth c3_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_7578 c1_depth c3_depth))

theorem normalization_7583 (c1_depth c3_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_7581 c1_depth c3_depth) (normalization_7582 c1_depth c3_depth))

theorem normalization_7584 (c1_depth c3_depth : Int) : (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_7583 c1_depth c3_depth))

abbrev shared_expr_Classification090_32 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))))
theorem normalization_7585 (c1_depth c3_depth : Int) : (formula_2371 c1_depth c3_depth) ↔ (shared_expr_Classification090_32 c1_depth c3_depth) := (iff_congr (normalization_7579 c1_depth c3_depth) (normalization_7584 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5838 (c1_depth c3_depth : Int) : (formula_2371 c1_depth c3_depth) := by
  classical
  have ht := (normalized_2133 ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7585 c1_depth c3_depth) hn

theorem normalized_2134 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7586 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Classification090_32 c1_depth c3_depth) := (iff_congr (normalization_7500 c1_depth c3_depth) (normalization_7584 c1_depth c3_depth))

-- Checked replay of trans.
theorem replay_5839 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_2134 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Classification090_32 c1_depth c3_depth))
  have n0 : (shared_expr_Classification090_30 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7580 c1_depth c3_depth) (replay_5837 c1_depth c3_depth)
  have n1 : (shared_expr_Classification090_32 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7585 c1_depth c3_depth) (replay_5838 c1_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7586 c1_depth c3_depth) hn

theorem normalized_2135 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7587 (c1_node c3_node : Int) : ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7588 (c1_node c3_node : Int) : (((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (and_congr (normalization_7587 c1_node c3_node) (normalization_7502 c1_node c3_node))

abbrev shared_expr_Classification090_33 (c1_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_7589 (c1_node c3_node : Int) : (((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification090_33 c1_node c3_node) := (iff_congr (normalization_7501 c1_node c3_node) (normalization_7588 c1_node c3_node))

-- Checked replay of rewrite.
theorem replay_5840 (c1_node c3_node : Int) : (((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2135 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_7589 c1_node c3_node) hn

abbrev shared_expr_Classification090_34 (c1_node c3_node : Int) : Prop := ((((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2372 (c1_node c3_node : Int) : Prop := (shared_expr_Classification090_34 c1_node c3_node)

theorem normalized_2136 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7590 (c1_node c3_node : Int) : (¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7587 c1_node c3_node))

theorem normalization_7591 (c1_node c3_node : Int) : ((¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) := (or_congr (normalization_7590 c1_node c3_node) (normalization_7503 c1_node c3_node))

theorem normalization_7592 (c1_node c3_node : Int) : (¬ ((¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) := (not_congr (normalization_7591 c1_node c3_node))

abbrev shared_expr_Classification090_35 (c1_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))))
theorem normalization_7593 (c1_node c3_node : Int) : (formula_2372 c1_node c3_node) ↔ (shared_expr_Classification090_35 c1_node c3_node) := (iff_congr (normalization_7588 c1_node c3_node) (normalization_7592 c1_node c3_node))

-- Checked replay of rewrite.
theorem replay_5841 (c1_node c3_node : Int) : (formula_2372 c1_node c3_node) := by
  classical
  have ht := (normalized_2136 (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7593 c1_node c3_node) hn

abbrev shared_expr_Classification090_36 (c1_node c3_node : Int) : Prop := (((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2373 (c1_node c3_node : Int) : Prop := (shared_expr_Classification090_36 c1_node c3_node)

theorem normalized_2137 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7594 (c1_node c3_node : Int) : (formula_2373 c1_node c3_node) ↔ (shared_expr_Classification090_35 c1_node c3_node) := (iff_congr (normalization_7501 c1_node c3_node) (normalization_7592 c1_node c3_node))

-- Checked replay of trans.
theorem replay_5842 (c1_node c3_node : Int) : (formula_2373 c1_node c3_node) := by
  classical
  have ht := (normalized_2137 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) (shared_expr_Classification090_35 c1_node c3_node))
  have n0 : (shared_expr_Classification090_33 c1_node c3_node) := by
    exact Iff.mp (normalization_7589 c1_node c3_node) (replay_5840 c1_node c3_node)
  have n1 : (shared_expr_Classification090_35 c1_node c3_node) := by
    exact Iff.mp (normalization_7593 c1_node c3_node) (replay_5841 c1_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7594 c1_node c3_node) hn

abbrev shared_expr_Classification090_37 (c1_node c1_sign c3_node : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))))
abbrev shared_expr_Classification090_38 (c1_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2374 (c1_node c1_sign c3_node : Int) : Prop := ((shared_expr_Classification090_37 c1_node c1_sign c3_node) ∨ (shared_expr_Classification090_38 c1_node c3_node))

theorem normalized_2138 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_39 (c1_node c1_sign c3_node : Int) : Prop := ((¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Classification090_40 (c1_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_7595 (c1_node c1_sign c3_node : Int) : (formula_2374 c1_node c1_sign c3_node) ↔ ((shared_expr_Classification090_39 c1_node c1_sign c3_node) ∨ (shared_expr_Classification090_40 c1_node c3_node)) := (or_congr (and_congr (normalization_7592 c1_node c3_node) (normalization_1600 c1_sign)) (and_congr (not_congr (normalization_7592 c1_node c3_node)) (normalization_7503 c1_node c3_node)))

abbrev shared_expr_Classification090_41 (c1_node c3_node : Int) : Prop := ((¬ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification090_42 (c1_node c1_sign c3_node : Int) : Prop := ((((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Classification090_41 c1_node c3_node))
theorem normalization_7596 (c1_node c1_sign c3_node : Int) : ((formula_2356 c1_node c1_sign c3_node) ↔ (formula_2374 c1_node c1_sign c3_node)) ↔ ((shared_expr_Classification090_42 c1_node c1_sign c3_node) ↔ ((shared_expr_Classification090_39 c1_node c1_sign c3_node) ∨ (shared_expr_Classification090_40 c1_node c3_node))) := (iff_congr (normalization_7504 c1_node c1_sign c3_node) (normalization_7595 c1_node c1_sign c3_node))

-- Checked replay of monotonicity.
theorem replay_5843 (c1_node c1_sign c3_node : Int) : ((formula_2356 c1_node c1_sign c3_node) ↔ (formula_2374 c1_node c1_sign c3_node)) := by
  classical
  have ht := (normalized_2138 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Classification090_35 c1_node c3_node) := by
    exact Iff.mp (normalization_7594 c1_node c3_node) (replay_5842 c1_node c3_node)
  have n1 : ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1698 c1_sign) (replay_636 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7596 c1_node c1_sign c3_node) hn

theorem normalized_2139 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_43 (c1_node c3_node : Int) : Prop := (((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_7597 (c1_node c1_sign c3_node : Int) : (formula_2330 c1_node c1_sign c3_node) ↔ ((shared_expr_Classification090_43 c1_node c3_node) ∨ (shared_expr_Classification090_39 c1_node c1_sign c3_node)) := (or_congr (and_congr (normalization_7591 c1_node c3_node) (normalization_7503 c1_node c3_node)) (and_congr (not_congr (normalization_7591 c1_node c3_node)) (normalization_1600 c1_sign)))

abbrev shared_expr_Classification090_44 (c1_node c1_sign c3_node : Int) : Prop := (((shared_expr_Classification090_39 c1_node c1_sign c3_node) ∨ (shared_expr_Classification090_40 c1_node c3_node)) ↔ ((shared_expr_Classification090_43 c1_node c3_node) ∨ (shared_expr_Classification090_39 c1_node c1_sign c3_node)))
theorem normalization_7598 (c1_node c1_sign c3_node : Int) : ((formula_2374 c1_node c1_sign c3_node) ↔ (formula_2330 c1_node c1_sign c3_node)) ↔ (shared_expr_Classification090_44 c1_node c1_sign c3_node) := (iff_congr (normalization_7595 c1_node c1_sign c3_node) (normalization_7597 c1_node c1_sign c3_node))

-- Checked replay of rewrite.
theorem replay_5844 (c1_node c1_sign c3_node : Int) : ((formula_2374 c1_node c1_sign c3_node) ↔ (formula_2330 c1_node c1_sign c3_node)) := by
  classical
  have ht := (normalized_2139 ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7598 c1_node c1_sign c3_node) hn

theorem normalized_2140 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7599 (c1_node c1_sign c3_node : Int) : ((formula_2356 c1_node c1_sign c3_node) ↔ (formula_2330 c1_node c1_sign c3_node)) ↔ ((shared_expr_Classification090_42 c1_node c1_sign c3_node) ↔ ((shared_expr_Classification090_43 c1_node c3_node) ∨ (shared_expr_Classification090_39 c1_node c1_sign c3_node))) := (iff_congr (normalization_7504 c1_node c1_sign c3_node) (normalization_7597 c1_node c1_sign c3_node))

-- Checked replay of trans.
theorem replay_5845 (c1_node c1_sign c3_node : Int) : ((formula_2356 c1_node c1_sign c3_node) ↔ (formula_2330 c1_node c1_sign c3_node)) := by
  classical
  have ht := (normalized_2140 (shared_expr_Classification090_42 c1_node c1_sign c3_node) ((shared_expr_Classification090_39 c1_node c1_sign c3_node) ∨ (shared_expr_Classification090_40 c1_node c3_node)) ((shared_expr_Classification090_43 c1_node c3_node) ∨ (shared_expr_Classification090_39 c1_node c1_sign c3_node)))
  have n0 : ((shared_expr_Classification090_42 c1_node c1_sign c3_node) ↔ ((shared_expr_Classification090_39 c1_node c1_sign c3_node) ∨ (shared_expr_Classification090_40 c1_node c3_node))) := by
    exact Iff.mp (normalization_7596 c1_node c1_sign c3_node) (replay_5843 c1_node c1_sign c3_node)
  have n1 : (shared_expr_Classification090_44 c1_node c1_sign c3_node) := by
    exact Iff.mp (normalization_7598 c1_node c1_sign c3_node) (replay_5844 c1_node c1_sign c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7599 c1_node c1_sign c3_node) hn

theorem normalized_2141 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7600 (c1_depth c3_depth : Int) : ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_7601 (c1_depth c3_depth : Int) : ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_7602 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (and_congr (normalization_7600 c1_depth c3_depth) (normalization_7601 c1_depth c3_depth))

abbrev shared_expr_Classification090_45 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
theorem normalization_7603 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification090_45 c1_depth c3_depth) := (iff_congr (normalization_7505 c1_depth c3_depth) (normalization_7602 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5846 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2141 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7603 c1_depth c3_depth) hn

abbrev shared_expr_Classification090_46 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))
abbrev formula_2375 (c1_depth c3_depth : Int) : Prop := (shared_expr_Classification090_46 c1_depth c3_depth)

theorem normalized_2142 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7604 (c1_depth c3_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := (not_congr (normalization_7600 c1_depth c3_depth))

theorem normalization_7605 (c1_depth c3_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (not_congr (normalization_7601 c1_depth c3_depth))

theorem normalization_7606 (c1_depth c3_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) := (or_congr (normalization_7604 c1_depth c3_depth) (normalization_7605 c1_depth c3_depth))

theorem normalization_7607 (c1_depth c3_depth : Int) : (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))) := (not_congr (normalization_7606 c1_depth c3_depth))

abbrev shared_expr_Classification090_47 (c1_depth c3_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))))
theorem normalization_7608 (c1_depth c3_depth : Int) : (formula_2375 c1_depth c3_depth) ↔ (shared_expr_Classification090_47 c1_depth c3_depth) := (iff_congr (normalization_7602 c1_depth c3_depth) (normalization_7607 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5847 (c1_depth c3_depth : Int) : (formula_2375 c1_depth c3_depth) := by
  classical
  have ht := (normalized_2142 ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7608 c1_depth c3_depth) hn

theorem normalized_2143 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7609 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification090_47 c1_depth c3_depth) := (iff_congr (normalization_7505 c1_depth c3_depth) (normalization_7607 c1_depth c3_depth))

-- Checked replay of trans.
theorem replay_5848 (c1_depth c3_depth : Int) : (((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2143 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (shared_expr_Classification090_47 c1_depth c3_depth))
  have n0 : (shared_expr_Classification090_45 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7603 c1_depth c3_depth) (replay_5846 c1_depth c3_depth)
  have n1 : (shared_expr_Classification090_47 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7608 c1_depth c3_depth) (replay_5847 c1_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7609 c1_depth c3_depth) hn

theorem normalized_2144 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7610 (c1_depth c3_depth : Int) : (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))) := (not_congr (normalization_7607 c1_depth c3_depth))

abbrev shared_expr_Classification090_48 (c1_depth c3_depth : Int) : Prop := ((¬ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))))
theorem normalization_7611 (c1_depth c3_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))) ↔ (shared_expr_Classification090_48 c1_depth c3_depth) := (iff_congr (normalization_7506 c1_depth c3_depth) (normalization_7610 c1_depth c3_depth))

-- Checked replay of monotonicity.
theorem replay_5849 (c1_depth c3_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_2144 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification090_47 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7609 c1_depth c3_depth) (replay_5848 c1_depth c3_depth)
  have hn := ht n0
  exact Iff.mpr (normalization_7611 c1_depth c3_depth) hn

abbrev shared_expr_Classification090_49 (c1_depth c3_depth : Int) : Prop := ((¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))
abbrev formula_2376 (c1_depth c3_depth : Int) : Prop := (shared_expr_Classification090_49 c1_depth c3_depth)

theorem normalized_2145 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_50 (c1_depth c3_depth : Int) : Prop := ((¬ (¬ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
theorem normalization_7612 (c1_depth c3_depth : Int) : (formula_2376 c1_depth c3_depth) ↔ (shared_expr_Classification090_50 c1_depth c3_depth) := (iff_congr (normalization_7610 c1_depth c3_depth) (normalization_7606 c1_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5850 (c1_depth c3_depth : Int) : (formula_2376 c1_depth c3_depth) := by
  classical
  have ht := (normalized_2145 ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_7612 c1_depth c3_depth) hn

theorem normalized_2146 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_51 (c1_depth c3_depth : Int) : Prop := ((¬ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
theorem normalization_7613 (c1_depth c3_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (shared_expr_Classification090_51 c1_depth c3_depth) := (iff_congr (normalization_7506 c1_depth c3_depth) (normalization_7606 c1_depth c3_depth))

-- Checked replay of trans.
theorem replay_5851 (c1_depth c3_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) := by
  classical
  have ht := (normalized_2146 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification090_48 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7611 c1_depth c3_depth) (replay_5849 c1_depth c3_depth)
  have n1 : (shared_expr_Classification090_50 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7612 c1_depth c3_depth) (replay_5850 c1_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7613 c1_depth c3_depth) hn

theorem normalized_2147 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7614 (c1_node c3_node : Int) : ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7615 (c1_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (and_congr (normalization_7508 c1_node c3_node) (normalization_7614 c1_node c3_node))

abbrev shared_expr_Classification090_52 (c1_node c3_node : Int) : Prop := (((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
theorem normalization_7616 (c1_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification090_52 c1_node c3_node) := (iff_congr (normalization_7507 c1_node c3_node) (normalization_7615 c1_node c3_node))

-- Checked replay of rewrite.
theorem replay_5852 (c1_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2147 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_7616 c1_node c3_node) hn

abbrev shared_expr_Classification090_53 (c1_node c3_node : Int) : Prop := ((((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2377 (c1_node c3_node : Int) : Prop := (shared_expr_Classification090_53 c1_node c3_node)

theorem normalized_2148 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7617 (c1_node c3_node : Int) : (¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_7614 c1_node c3_node))

theorem normalization_7618 (c1_node c3_node : Int) : ((¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) := (or_congr (normalization_7509 c1_node c3_node) (normalization_7617 c1_node c3_node))

theorem normalization_7619 (c1_node c3_node : Int) : (¬ ((¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) := (not_congr (normalization_7618 c1_node c3_node))

abbrev shared_expr_Classification090_54 (c1_node c3_node : Int) : Prop := (((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))))
theorem normalization_7620 (c1_node c3_node : Int) : (formula_2377 c1_node c3_node) ↔ (shared_expr_Classification090_54 c1_node c3_node) := (iff_congr (normalization_7615 c1_node c3_node) (normalization_7619 c1_node c3_node))

-- Checked replay of rewrite.
theorem replay_5853 (c1_node c3_node : Int) : (formula_2377 c1_node c3_node) := by
  classical
  have ht := (normalized_2148 (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7620 c1_node c3_node) hn

abbrev shared_expr_Classification090_55 (c1_node c3_node : Int) : Prop := (((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2378 (c1_node c3_node : Int) : Prop := (shared_expr_Classification090_55 c1_node c3_node)

theorem normalized_2149 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7621 (c1_node c3_node : Int) : (formula_2378 c1_node c3_node) ↔ (shared_expr_Classification090_54 c1_node c3_node) := (iff_congr (normalization_7507 c1_node c3_node) (normalization_7619 c1_node c3_node))

-- Checked replay of trans.
theorem replay_5854 (c1_node c3_node : Int) : (formula_2378 c1_node c3_node) := by
  classical
  have ht := (normalized_2149 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) (shared_expr_Classification090_54 c1_node c3_node))
  have n0 : (shared_expr_Classification090_52 c1_node c3_node) := by
    exact Iff.mp (normalization_7616 c1_node c3_node) (replay_5852 c1_node c3_node)
  have n1 : (shared_expr_Classification090_54 c1_node c3_node) := by
    exact Iff.mp (normalization_7620 c1_node c3_node) (replay_5853 c1_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7621 c1_node c3_node) hn

abbrev shared_expr_Classification090_56 (c1_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification090_57 (c1_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_2379 (c1_node c3_node c3_sign : Int) : Prop := ((shared_expr_Classification090_56 c1_node c3_node c3_sign) ∨ (shared_expr_Classification090_57 c1_node c3_node))

theorem normalized_2150 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_58 (c1_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification090_59 (c1_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))))) ∧ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_7622 (c1_node c3_node c3_sign : Int) : (formula_2379 c1_node c3_node c3_sign) ↔ ((shared_expr_Classification090_58 c1_node c3_node c3_sign) ∨ (shared_expr_Classification090_59 c1_node c3_node)) := (or_congr (and_congr (normalization_7619 c1_node c3_node) (normalization_6849 c3_sign)) (and_congr (not_congr (normalization_7619 c1_node c3_node)) (normalization_7509 c1_node c3_node)))

abbrev shared_expr_Classification090_60 (c1_node c3_node : Int) : Prop := ((¬ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification090_61 (c1_node c3_node c3_sign : Int) : Prop := ((((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification090_60 c1_node c3_node))
theorem normalization_7623 (c1_node c3_node c3_sign : Int) : ((formula_2357 c1_node c3_node c3_sign) ↔ (formula_2379 c1_node c3_node c3_sign)) ↔ ((shared_expr_Classification090_61 c1_node c3_node c3_sign) ↔ ((shared_expr_Classification090_58 c1_node c3_node c3_sign) ∨ (shared_expr_Classification090_59 c1_node c3_node))) := (iff_congr (normalization_7510 c1_node c3_node c3_sign) (normalization_7622 c1_node c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5855 (c1_node c3_node c3_sign : Int) : ((formula_2357 c1_node c3_node c3_sign) ↔ (formula_2379 c1_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2150 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification090_54 c1_node c3_node) := by
    exact Iff.mp (normalization_7621 c1_node c3_node) (replay_5854 c1_node c3_node)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6942 c3_sign) (replay_4980 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7623 c1_node c3_node c3_sign) hn

theorem normalized_2151 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_62 (c1_node c3_node : Int) : Prop := (((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_7624 (c1_node c3_node c3_sign : Int) : (formula_2329 c1_node c3_node c3_sign) ↔ ((shared_expr_Classification090_62 c1_node c3_node) ∨ (shared_expr_Classification090_58 c1_node c3_node c3_sign)) := (or_congr (and_congr (normalization_7618 c1_node c3_node) (normalization_7509 c1_node c3_node)) (and_congr (not_congr (normalization_7618 c1_node c3_node)) (normalization_6849 c3_sign)))

abbrev shared_expr_Classification090_63 (c1_node c3_node c3_sign : Int) : Prop := (((shared_expr_Classification090_58 c1_node c3_node c3_sign) ∨ (shared_expr_Classification090_59 c1_node c3_node)) ↔ ((shared_expr_Classification090_62 c1_node c3_node) ∨ (shared_expr_Classification090_58 c1_node c3_node c3_sign)))
theorem normalization_7625 (c1_node c3_node c3_sign : Int) : ((formula_2379 c1_node c3_node c3_sign) ↔ (formula_2329 c1_node c3_node c3_sign)) ↔ (shared_expr_Classification090_63 c1_node c3_node c3_sign) := (iff_congr (normalization_7622 c1_node c3_node c3_sign) (normalization_7624 c1_node c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5856 (c1_node c3_node c3_sign : Int) : ((formula_2379 c1_node c3_node c3_sign) ↔ (formula_2329 c1_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2151 ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) (((c1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7625 c1_node c3_node c3_sign) hn

theorem normalized_2152 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7626 (c1_node c3_node c3_sign : Int) : ((formula_2357 c1_node c3_node c3_sign) ↔ (formula_2329 c1_node c3_node c3_sign)) ↔ ((shared_expr_Classification090_61 c1_node c3_node c3_sign) ↔ ((shared_expr_Classification090_62 c1_node c3_node) ∨ (shared_expr_Classification090_58 c1_node c3_node c3_sign))) := (iff_congr (normalization_7510 c1_node c3_node c3_sign) (normalization_7624 c1_node c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5857 (c1_node c3_node c3_sign : Int) : ((formula_2357 c1_node c3_node c3_sign) ↔ (formula_2329 c1_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2152 (shared_expr_Classification090_61 c1_node c3_node c3_sign) ((shared_expr_Classification090_58 c1_node c3_node c3_sign) ∨ (shared_expr_Classification090_59 c1_node c3_node)) ((shared_expr_Classification090_62 c1_node c3_node) ∨ (shared_expr_Classification090_58 c1_node c3_node c3_sign)))
  have n0 : ((shared_expr_Classification090_61 c1_node c3_node c3_sign) ↔ ((shared_expr_Classification090_58 c1_node c3_node c3_sign) ∨ (shared_expr_Classification090_59 c1_node c3_node))) := by
    exact Iff.mp (normalization_7623 c1_node c3_node c3_sign) (replay_5855 c1_node c3_node c3_sign)
  have n1 : (shared_expr_Classification090_63 c1_node c3_node c3_sign) := by
    exact Iff.mp (normalization_7625 c1_node c3_node c3_sign) (replay_5856 c1_node c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7626 c1_node c3_node c3_sign) hn

abbrev shared_expr_Classification090_64 (c1_depth c1_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_2357 c1_node c3_node c3_sign)) ↔ (((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_2329 c1_node c3_node c3_sign)))
abbrev formula_2380 (c1_depth c1_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification090_64 c1_depth c1_node c3_depth c3_node c3_sign)

theorem normalized_2153 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification090_65 (c1_depth c1_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ ((shared_expr_Classification090_62 c1_node c3_node) ∨ (shared_expr_Classification090_58 c1_node c3_node c3_sign)))
theorem normalization_7627 (c1_depth c1_node c3_depth c3_node c3_sign : Int) : (((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_2329 c1_node c3_node c3_sign)) ↔ (shared_expr_Classification090_65 c1_depth c1_node c3_depth c3_node c3_sign) := (or_congr (normalization_7606 c1_depth c3_depth) (normalization_7624 c1_node c3_node c3_sign))

abbrev shared_expr_Classification090_66 (c1_depth c1_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification090_61 c1_node c3_node c3_sign)) ↔ (shared_expr_Classification090_65 c1_depth c1_node c3_depth c3_node c3_sign))
theorem normalization_7628 (c1_depth c1_node c3_depth c3_node c3_sign : Int) : (formula_2380 c1_depth c1_node c3_depth c3_node c3_sign) ↔ (shared_expr_Classification090_66 c1_depth c1_node c3_depth c3_node c3_sign) := (iff_congr (normalization_7511 c1_depth c1_node c3_depth c3_node c3_sign) (normalization_7627 c1_depth c1_node c3_depth c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5858 (c1_depth c1_node c3_depth c3_node c3_sign : Int) : (formula_2380 c1_depth c1_node c3_depth c3_node c3_sign) := by
  classical
  have ht := (normalized_2153 (((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) (shared_expr_Classification090_61 c1_node c3_node c3_sign) ((shared_expr_Classification090_62 c1_node c3_node) ∨ (shared_expr_Classification090_58 c1_node c3_node c3_sign)))
  have n0 : (shared_expr_Classification090_51 c1_depth c3_depth) := by
    exact Iff.mp (normalization_7613 c1_depth c3_depth) (replay_5851 c1_depth c3_depth)
  have n1 : ((shared_expr_Classification090_61 c1_node c3_node c3_sign) ↔ ((shared_expr_Classification090_62 c1_node c3_node) ∨ (shared_expr_Classification090_58 c1_node c3_node c3_sign))) := by
    exact Iff.mp (normalization_7626 c1_node c3_node c3_sign) (replay_5857 c1_node c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7628 c1_depth c1_node c3_depth c3_node c3_sign) hn

end H4Formal.Generated.Classification
