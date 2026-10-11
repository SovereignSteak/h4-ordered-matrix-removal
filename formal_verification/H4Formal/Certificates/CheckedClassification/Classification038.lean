import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification037

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Classification038_0 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_1383 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1312 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
abbrev formula_1385 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification038_0 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

theorem normalized_1096 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_1 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
abbrev shared_expr_Classification038_2 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification038_1 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
abbrev shared_expr_Classification038_3 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
abbrev shared_expr_Classification038_4 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification038_3 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
abbrev shared_expr_Classification038_5 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification038_6 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification038_5 c1_depth c1_kind c1_node c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_1 c1_depth c1_kind c1_sign r3_level))))
abbrev shared_expr_Classification038_7 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification038_8 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification038_7 c1_depth c1_kind c1_node c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_1 c1_depth c1_kind c1_sign r3_level))))
abbrev shared_expr_Classification038_9 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification038_10 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification038_3 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_9 c1_depth c1_kind c1_node c1_sign r3_level))))
abbrev shared_expr_Classification038_11 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification038_12 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification038_3 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_11 c1_depth c1_kind c1_node c1_sign r3_level))))
abbrev shared_expr_Classification038_13 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification038_2 c1_depth c1_kind c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification038_4 c1_depth c1_kind c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification038_6 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification038_8 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification038_10 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification038_12 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))))
abbrev shared_expr_Classification038_14 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
abbrev shared_expr_Classification038_15 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification038_13 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) ∨ ((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification038_14 c1_group c1_level c1_mode r3_group r3_level r3_mode))))
theorem normalization_4731 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1312 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification038_15 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_1522 c1_kind) (normalization_4727 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_1522 c1_kind)) (normalization_4680 c1_group c1_level c1_mode r3_group r3_level r3_mode)))

abbrev shared_expr_Classification038_16 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification038_14 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification038_13 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Classification038_17 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification038_16 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification038_15 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
theorem normalization_4732 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1385 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification038_17 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (iff_congr (normalization_4729 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (normalization_4731 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_1908 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1385 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_1096 ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Classification038_14 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Classification038_13 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))
  have hn := ht
  exact Iff.mpr (normalization_4732 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) hn

abbrev shared_expr_Classification038_18 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_1368 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1312 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
abbrev formula_1386 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification038_18 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

theorem normalized_1097 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_19 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := (((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
abbrev shared_expr_Classification038_20 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_21 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_20 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification038_22 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_23 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_22 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification038_24 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification038_25 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_20 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_24 c1_depth c1_kind c1_node c1_sign r3_level)))
abbrev shared_expr_Classification038_26 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification038_27 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_20 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_26 c1_depth c1_kind c1_node c1_sign r3_level)))
abbrev shared_expr_Classification038_28 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification038_29 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_28 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_22 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification038_30 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification038_31 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_30 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_22 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification038_32 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification038_21 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_23 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification038_25 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification038_27 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification038_29 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification038_31 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))
abbrev shared_expr_Classification038_33 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification038_19 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification038_32 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Classification038_34 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification038_33 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification038_15 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
theorem normalization_4733 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1386 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification038_34 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (iff_congr (normalization_4593 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (normalization_4731 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))

-- Checked replay of trans.
abbrev shared_expr_Classification038_35 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification038_33 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification038_16 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
theorem replay_1909 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1386 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_1097 (shared_expr_Classification038_33 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (shared_expr_Classification038_16 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (shared_expr_Classification038_15 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
  have n0 : (shared_expr_Classification038_35 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_4730 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (replay_1907 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)
  have n1 : (shared_expr_Classification038_17 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_4732 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (replay_1908 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4733 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_1910 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1371 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (formula_1059 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) := by
  classical
  first
  | (simp only [formula_1371, shared_expr_Classification037_87, formula_1369, shared_expr_Classification037_85, formula_1370, shared_expr_Classification037_86, formula_1345, shared_expr_Classification036_56, formula_1346, shared_expr_Classification036_57, formula_1347, shared_expr_Classification036_58, formula_1348, shared_expr_Classification036_59, formula_1059, shared_expr_Classification030_31, formula_1049, shared_expr_Classification030_21, formula_1047, shared_expr_Classification030_19, formula_1048, shared_expr_Classification030_20, formula_1052, shared_expr_Classification030_24, formula_1050, shared_expr_Classification030_22, formula_1051, shared_expr_Classification030_23, formula_1054, shared_expr_Classification030_26, formula_1053, shared_expr_Classification030_25, formula_1056, shared_expr_Classification030_28, formula_1055, shared_expr_Classification030_27, formula_1058, shared_expr_Classification030_30, formula_1057, shared_expr_Classification030_29, formula_1046, shared_expr_Classification030_18, formula_1045, shared_expr_Classification030_17, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_1098 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4734 (c1_depth r3_depth : Int) : (r3_depth ≤ c1_depth) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4735 (c1_depth r3_depth : Int) : (r3_depth ≥ c1_depth) ↔ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4736 (c1_depth r3_depth : Int) : ((r3_depth ≤ c1_depth) ∧ (r3_depth ≥ c1_depth)) ↔ ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (and_congr (normalization_4734 c1_depth r3_depth) (normalization_4735 c1_depth r3_depth))

abbrev shared_expr_Classification038_36 (c1_depth r3_depth : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_4737 (c1_depth r3_depth : Int) : ((r3_depth = c1_depth) ↔ ((r3_depth ≤ c1_depth) ∧ (r3_depth ≥ c1_depth))) ↔ (shared_expr_Classification038_36 c1_depth r3_depth) := (iff_congr (normalization_4492 c1_depth r3_depth) (normalization_4736 c1_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_1911 (c1_depth r3_depth : Int) : ((r3_depth = c1_depth) ↔ ((r3_depth ≤ c1_depth) ∧ (r3_depth ≥ c1_depth))) := by
  classical
  have ht := (normalized_1098 ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4737 c1_depth r3_depth) hn

theorem normalized_1099 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4738 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4739 (c1_depth r3_depth : Int) : ((r3_depth ≤ c1_depth) ↔ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_4734 c1_depth r3_depth) (normalization_4738 c1_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_1912 (c1_depth r3_depth : Int) : ((r3_depth ≤ c1_depth) ↔ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1099 ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4739 c1_depth r3_depth) hn

theorem normalized_1100 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4740 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4741 (c1_depth r3_depth : Int) : ((r3_depth ≥ c1_depth) ↔ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (iff_congr (normalization_4735 c1_depth r3_depth) (normalization_4740 c1_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_1913 (c1_depth r3_depth : Int) : ((r3_depth ≥ c1_depth) ↔ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1100 ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4741 c1_depth r3_depth) hn

theorem normalized_1101 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4742 (c1_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (and_congr (normalization_4738 c1_depth r3_depth) (normalization_4740 c1_depth r3_depth))

theorem normalization_4743 (c1_depth r3_depth : Int) : (((r3_depth ≤ c1_depth) ∧ (r3_depth ≥ c1_depth)) ↔ (((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification038_36 c1_depth r3_depth) := (iff_congr (normalization_4736 c1_depth r3_depth) (normalization_4742 c1_depth r3_depth))

-- Checked replay of monotonicity.
theorem replay_1914 (c1_depth r3_depth : Int) : (((r3_depth ≤ c1_depth) ∧ (r3_depth ≥ c1_depth)) ↔ (((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1101 ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4739 c1_depth r3_depth) (replay_1912 c1_depth r3_depth)
  have n1 : (((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4741 c1_depth r3_depth) (replay_1913 c1_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4743 c1_depth r3_depth) hn

abbrev shared_expr_Classification038_37 (c1_depth r3_depth : Int) : Prop := ((((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))))
abbrev formula_1387 (c1_depth r3_depth : Int) : Prop := (shared_expr_Classification038_37 c1_depth r3_depth)

theorem normalized_1102 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4744 (c1_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_4738 c1_depth r3_depth))

theorem normalization_4745 (c1_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (not_congr (normalization_4740 c1_depth r3_depth))

theorem normalization_4746 (c1_depth r3_depth : Int) : ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := (or_congr (normalization_4744 c1_depth r3_depth) (normalization_4745 c1_depth r3_depth))

theorem normalization_4747 (c1_depth r3_depth : Int) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))) := (not_congr (normalization_4746 c1_depth r3_depth))

abbrev shared_expr_Classification038_38 (c1_depth r3_depth : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))))
theorem normalization_4748 (c1_depth r3_depth : Int) : (formula_1387 c1_depth r3_depth) ↔ (shared_expr_Classification038_38 c1_depth r3_depth) := (iff_congr (normalization_4742 c1_depth r3_depth) (normalization_4747 c1_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_1915 (c1_depth r3_depth : Int) : (formula_1387 c1_depth r3_depth) := by
  classical
  have ht := (normalized_1102 ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4748 c1_depth r3_depth) hn

theorem normalized_1103 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4749 (c1_depth r3_depth : Int) : (((r3_depth ≤ c1_depth) ∧ (r3_depth ≥ c1_depth)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification038_38 c1_depth r3_depth) := (iff_congr (normalization_4736 c1_depth r3_depth) (normalization_4747 c1_depth r3_depth))

-- Checked replay of trans.
theorem replay_1916 (c1_depth r3_depth : Int) : (((r3_depth ≤ c1_depth) ∧ (r3_depth ≥ c1_depth)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1103 ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (shared_expr_Classification038_38 c1_depth r3_depth))
  have n0 : (shared_expr_Classification038_36 c1_depth r3_depth) := by
    exact Iff.mp (normalization_4743 c1_depth r3_depth) (replay_1914 c1_depth r3_depth)
  have n1 : (shared_expr_Classification038_38 c1_depth r3_depth) := by
    exact Iff.mp (normalization_4748 c1_depth r3_depth) (replay_1915 c1_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4749 c1_depth r3_depth) hn

theorem normalized_1104 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4750 (c1_depth r3_depth : Int) : ((r3_depth = c1_depth) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification038_38 c1_depth r3_depth) := (iff_congr (normalization_4492 c1_depth r3_depth) (normalization_4747 c1_depth r3_depth))

-- Checked replay of trans.
theorem replay_1917 (c1_depth r3_depth : Int) : ((r3_depth = c1_depth) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1104 ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (shared_expr_Classification038_38 c1_depth r3_depth))
  have n0 : (shared_expr_Classification038_36 c1_depth r3_depth) := by
    exact Iff.mp (normalization_4737 c1_depth r3_depth) (replay_1911 c1_depth r3_depth)
  have n1 : (shared_expr_Classification038_38 c1_depth r3_depth) := by
    exact Iff.mp (normalization_4749 c1_depth r3_depth) (replay_1916 c1_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4750 c1_depth r3_depth) hn

abbrev shared_expr_Classification038_39 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((r3_sign = (0 : Int)) ∧ (c1_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev formula_1388 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_39 c1_node c1_sign r3_node r3_sign)

theorem normalized_1105 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4751 (c1_node c1_sign r3_node r3_sign : Int) : ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_622 r3_sign) (and_congr (normalization_1600 c1_sign) (normalization_4602 c1_node r3_node)))

abbrev shared_expr_Classification038_40 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ↔ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))
theorem normalization_4752 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1388 c1_node c1_sign r3_node r3_sign) ↔ (shared_expr_Classification038_40 c1_node c1_sign r3_node r3_sign) := (iff_congr (normalization_4603 c1_node c1_sign r3_node r3_sign) (normalization_4751 c1_node c1_sign r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1918 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1388 c1_node c1_sign r3_node r3_sign) := by
  classical
  have ht := (normalized_1105 (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))) (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))) ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have n0 : ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_2651 r3_sign) (replay_976 r3_sign)
  have n1 : ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1698 c1_sign) (replay_636 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4752 c1_node c1_sign r3_node r3_sign) hn

abbrev shared_expr_Classification038_41 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))))
abbrev formula_1389 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_41 c1_node c1_sign r3_node r3_sign)

theorem normalized_1106 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4753 (c1_node r3_node : Int) : (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4602 c1_node r3_node))

theorem normalization_4754 (c1_node c1_sign r3_node r3_sign : Int) : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ↔ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_618 r3_sign) (or_congr (normalization_620 r3_sign) (or_congr (normalization_1596 c1_sign) (or_congr (normalization_1598 c1_sign) (normalization_4753 c1_node r3_node)))))

theorem normalization_4755 (c1_node c1_sign r3_node r3_sign : Int) : (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_4754 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Classification038_42 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))))
theorem normalization_4756 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1389 c1_node c1_sign r3_node r3_sign) ↔ (shared_expr_Classification038_42 c1_node c1_sign r3_node r3_sign) := (iff_congr (normalization_4751 c1_node c1_sign r3_node r3_sign) (normalization_4755 c1_node c1_sign r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1919 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1389 c1_node c1_sign r3_node r3_sign) := by
  classical
  have ht := (normalized_1106 ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)) ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4756 c1_node c1_sign r3_node r3_sign) hn

abbrev shared_expr_Classification038_43 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((r3_sign = (0 : Int)) ∧ (c1_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))))
abbrev formula_1390 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_43 c1_node c1_sign r3_node r3_sign)

theorem normalized_1107 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_44 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))))
theorem normalization_4757 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1390 c1_node c1_sign r3_node r3_sign) ↔ (shared_expr_Classification038_44 c1_node c1_sign r3_node r3_sign) := (iff_congr (normalization_4603 c1_node c1_sign r3_node r3_sign) (normalization_4755 c1_node c1_sign r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1920 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1390 c1_node c1_sign r3_node r3_sign) := by
  classical
  have ht := (normalized_1107 ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))))
  have n0 : (shared_expr_Classification038_40 c1_node c1_sign r3_node r3_sign) := by
    exact Iff.mp (normalization_4752 c1_node c1_sign r3_node r3_sign) (replay_1918 c1_node c1_sign r3_node r3_sign)
  have n1 : (shared_expr_Classification038_42 c1_node c1_sign r3_node r3_sign) := by
    exact Iff.mp (normalization_4756 c1_node c1_sign r3_node r3_sign) (replay_1919 c1_node c1_sign r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4757 c1_node c1_sign r3_node r3_sign) hn

abbrev shared_expr_Classification038_45 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
abbrev formula_1391 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_45 c1_node c1_sign h r3_depth r3_node r3_sign)

theorem normalized_1108 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∧ p2 ∧ p4 ∧ (¬ p6)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p5) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_46 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
theorem normalization_4758 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1391 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_46 c1_node c1_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2666 r3_sign) (and_congr (normalization_1606 c1_sign) (and_congr (normalization_2680 h r3_depth) (normalization_4602 c1_node r3_node))))

abbrev shared_expr_Classification038_47 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ∧ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
theorem normalization_4759 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (((r3_sign = (2 : Int)) ∧ (c1_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (formula_1391 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification038_47 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_46 c1_node c1_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_4604 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4758 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification038_48 (h r3_depth : Int) : Prop := (((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))))))
theorem replay_1921 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (((r3_sign = (2 : Int)) ∧ (c1_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (formula_1391 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_1108 (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))) (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))) ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))) ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))) ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have n0 : ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2668 r3_sign) (replay_982 r3_sign)
  have n1 : ((((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1709 c1_sign) (replay_642 c1_sign)
  have n2 : (shared_expr_Classification038_48 h r3_depth) := by
    exact Iff.mp (normalization_2683 h r3_depth) (replay_989 h r3_depth)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4759 c1_node c1_sign h r3_depth r3_node r3_sign) hn

theorem normalized_1109 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ ((¬ p4) ∨ (¬ (¬ p5)))) ∧ (¬ p6)) ↔ (¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p6))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_49 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))) ∨ (¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))
theorem normalization_4760 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2469 h r3_depth) (or_congr (normalization_2678 h r3_depth) (or_congr (normalization_2663 r3_sign) (or_congr (normalization_2664 r3_sign) (or_congr (normalization_1602 c1_sign) (or_congr (normalization_1604 c1_sign) (normalization_4753 c1_node r3_node)))))))

theorem normalization_4761 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_4760 c1_node c1_sign h r3_depth r3_node r3_sign))

theorem normalization_4762 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1391 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign))) ↔ ((shared_expr_Classification038_46 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_4758 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4761 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1922 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1391 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign))) := by
  classical
  have ht := (normalized_1109 ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)) ((c1_sign) ≤ (2 : Int)) ((c1_sign) ≤ (1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4762 c1_node c1_sign h r3_depth r3_node r3_sign) hn

theorem normalized_1110 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4763 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (((r3_sign = (2 : Int)) ∧ (c1_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign))) ↔ ((shared_expr_Classification038_47 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_4604 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4761 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1923 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (((r3_sign = (2 : Int)) ∧ (c1_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign))) := by
  classical
  have ht := (normalized_1110 (shared_expr_Classification038_47 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_46 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign))
  have n0 : ((shared_expr_Classification038_47 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_46 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_4759 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1921 c1_node c1_sign h r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification038_46 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_4762 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1922 c1_node c1_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4763 c1_node c1_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification038_50 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))
abbrev formula_1392 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_50 c1_node c1_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Classification038_51 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_sign = (1 : Int)) ∧ (c1_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ↔ (formula_1392 c1_node c1_sign h r3_depth r3_node r3_sign))
abbrev formula_1393 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_51 c1_node c1_sign h r3_depth r3_node r3_sign)

theorem normalized_1111 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4) ∧ (¬ p5)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4) ∧ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_52 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
theorem normalization_4764 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1392 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_52 c1_node c1_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2697 r3_sign) (and_congr (normalization_1626 c1_sign) (and_congr (normalization_2469 h r3_depth) (normalization_4606 c1_node r3_node))))

abbrev shared_expr_Classification038_53 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
theorem normalization_4765 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1393 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ ((shared_expr_Classification038_53 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_52 c1_node c1_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_4607 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4764 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1924 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1393 c1_node c1_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_1111 (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))) (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)))
  have n0 : ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_2699 r3_sign) (replay_995 r3_sign)
  have n1 : ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1719 c1_sign) (replay_648 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4765 c1_node c1_sign h r3_depth r3_node r3_sign) hn

theorem normalized_1112 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4) ∧ (¬ p5)) ↔ (¬ (p4 ∨ p5 ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_54 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ∨ ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ∨ (¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))
theorem normalization_4766 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2468 h r3_depth) (or_congr (normalization_4605 c1_node r3_node) (or_congr (normalization_2694 r3_sign) (or_congr (normalization_2695 r3_sign) (or_congr (normalization_1622 c1_sign) (normalization_1624 c1_sign))))))

theorem normalization_4767 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_4766 c1_node c1_sign h r3_depth r3_node r3_sign))

theorem normalization_4768 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1392 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign))) ↔ ((shared_expr_Classification038_52 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_4764 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4767 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1925 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1392 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign))) := by
  classical
  have ht := (normalized_1112 ((r3_sign) ≤ (1 : Int)) ((r3_sign) ≤ (0 : Int)) ((c1_sign) ≤ (1 : Int)) ((c1_sign) ≤ (0 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4768 c1_node c1_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification038_55 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_sign = (1 : Int)) ∧ (c1_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ↔ (¬ (formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign)))
abbrev formula_1394 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_55 c1_node c1_sign h r3_depth r3_node r3_sign)

theorem normalized_1113 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4769 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1394 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ ((shared_expr_Classification038_53 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_4607 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4767 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1926 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1394 c1_node c1_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_1113 (shared_expr_Classification038_53 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_52 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign))
  have n0 : ((shared_expr_Classification038_53 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_52 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_4765 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1924 c1_node c1_sign h r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification038_52 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_4768 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1925 c1_node c1_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4769 c1_node c1_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification038_56 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ∨ (¬ (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign)))
abbrev formula_1395 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_56 c1_node c1_sign h r3_depth r3_node r3_sign)

theorem normalized_1114 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∨ p2 ∨ p4) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_57 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign)))
theorem normalization_4770 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1395 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_57 c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_4755 c1_node c1_sign r3_node r3_sign) (or_congr (normalization_4761 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4767 c1_node c1_sign h r3_depth r3_node r3_sign)))

abbrev shared_expr_Classification038_58 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification038_47 c1_node c1_sign h r3_depth r3_node r3_sign) ∨ (shared_expr_Classification038_53 c1_node c1_sign h r3_depth r3_node r3_sign))
theorem normalization_4771 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (formula_1395 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_57 c1_node c1_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_4608 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4770 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1927 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (formula_1395 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_1114 ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))) (shared_expr_Classification038_47 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_53 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign))
  have n0 : (shared_expr_Classification038_44 c1_node c1_sign r3_node r3_sign) := by
    exact Iff.mp (normalization_4757 c1_node c1_sign r3_node r3_sign) (replay_1920 c1_node c1_sign r3_node r3_sign)
  have n1 : ((shared_expr_Classification038_47 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_4763 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1923 c1_node c1_sign h r3_depth r3_node r3_sign)
  have n2 : ((shared_expr_Classification038_53 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_4769 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1926 c1_node c1_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4771 c1_node c1_sign h r3_depth r3_node r3_sign) hn

theorem normalized_1115 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ↔ ((¬ p1) ∨ (¬ p0) ∨ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_59 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign)))
theorem normalization_4772 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_4761 c1_node c1_sign h r3_depth r3_node r3_sign) (or_congr (normalization_4755 c1_node c1_sign r3_node r3_sign) (normalization_4767 c1_node c1_sign h r3_depth r3_node r3_sign)))

theorem normalization_4773 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1395 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification038_57 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_4770 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4772 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1928 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1395 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_1115 ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))) (shared_expr_Classification038_49 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_54 c1_node c1_sign h r3_depth r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_4773 c1_node c1_sign h r3_depth r3_node r3_sign) hn

theorem normalized_1116 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4774 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_4608 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4772 c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1929 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_1116 (shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_57 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign))
  have n0 : ((shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_57 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_4771 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1927 c1_node c1_sign h r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification038_57 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_4773 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1928 c1_node c1_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4774 c1_node c1_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification038_60 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_depth = c1_depth) ∧ (formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ ((¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ∧ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)))
abbrev formula_1396 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_60 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)

theorem normalized_1117 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_61 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign))
theorem normalization_4775 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ∧ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (shared_expr_Classification038_61 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_4747 c1_depth r3_depth) (normalization_4772 c1_node c1_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Classification038_62 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (shared_expr_Classification038_61 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))
theorem normalization_4776 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1396 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_62 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := (iff_congr (normalization_4609 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4775 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1930 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1396 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_1117 ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) (shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign))
  have n0 : (shared_expr_Classification038_38 c1_depth r3_depth) := by
    exact Iff.mp (normalization_4750 c1_depth r3_depth) (replay_1917 c1_depth r3_depth)
  have n1 : ((shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_4774 c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1929 c1_node c1_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4776 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification038_63 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ∧ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)))))
abbrev formula_1397 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_63 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)

theorem normalized_1118 (p0 p1 p2 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ p2) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4777 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_4772 c1_node c1_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Classification038_64 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign)))
theorem normalization_4778 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))) ↔ (shared_expr_Classification038_64 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_4744 c1_depth r3_depth) (or_congr (normalization_4745 c1_depth r3_depth) (normalization_4777 c1_node c1_sign h r3_depth r3_node r3_sign)))

theorem normalization_4779 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)))) ↔ (¬ (shared_expr_Classification038_64 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_4778 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))

theorem normalization_4780 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1397 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) ↔ ((shared_expr_Classification038_61 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_64 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_4775 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4779 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1931 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1397 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_1118 ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) (shared_expr_Classification038_59 c1_node c1_sign h r3_depth r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_4780 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification038_65 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_depth = c1_depth) ∧ (formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign)))))
abbrev formula_1398 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_65 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)

theorem normalized_1119 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_66 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_64 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)))
theorem normalization_4781 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1398 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_66 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := (iff_congr (normalization_4609 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4779 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1932 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1398 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_1119 (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign)) (shared_expr_Classification038_61 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_64 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))
  have n0 : (shared_expr_Classification038_62 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := by
    exact Iff.mp (normalization_4776 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1930 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification038_61 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_64 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_4780 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1931 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4781 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) hn

theorem normalized_1120 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4782 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_4783 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_4784 (c1_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := (and_congr (normalization_4782 c1_depth r3_depth) (normalization_4783 c1_depth r3_depth))

abbrev shared_expr_Classification038_67 (c1_depth r3_depth : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))
theorem normalization_4785 (c1_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification038_67 c1_depth r3_depth) := (iff_congr (normalization_4610 c1_depth r3_depth) (normalization_4784 c1_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_1933 (c1_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1120 ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4785 c1_depth r3_depth) hn

abbrev shared_expr_Classification038_68 (c1_depth r3_depth : Int) : Prop := ((((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))))
abbrev formula_1399 (c1_depth r3_depth : Int) : Prop := (shared_expr_Classification038_68 c1_depth r3_depth)

theorem normalized_1121 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4786 (c1_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_4782 c1_depth r3_depth))

theorem normalization_4787 (c1_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := (not_congr (normalization_4783 c1_depth r3_depth))

theorem normalization_4788 (c1_depth r3_depth : Int) : ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (or_congr (normalization_4786 c1_depth r3_depth) (normalization_4787 c1_depth r3_depth))

theorem normalization_4789 (c1_depth r3_depth : Int) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))) := (not_congr (normalization_4788 c1_depth r3_depth))

abbrev shared_expr_Classification038_69 (c1_depth r3_depth : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))))
theorem normalization_4790 (c1_depth r3_depth : Int) : (formula_1399 c1_depth r3_depth) ↔ (shared_expr_Classification038_69 c1_depth r3_depth) := (iff_congr (normalization_4784 c1_depth r3_depth) (normalization_4789 c1_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_1934 (c1_depth r3_depth : Int) : (formula_1399 c1_depth r3_depth) := by
  classical
  have ht := (normalized_1121 ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4790 c1_depth r3_depth) hn

theorem normalized_1122 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4791 (c1_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification038_69 c1_depth r3_depth) := (iff_congr (normalization_4610 c1_depth r3_depth) (normalization_4789 c1_depth r3_depth))

-- Checked replay of trans.
theorem replay_1935 (c1_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1122 ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) (shared_expr_Classification038_69 c1_depth r3_depth))
  have n0 : (shared_expr_Classification038_67 c1_depth r3_depth) := by
    exact Iff.mp (normalization_4785 c1_depth r3_depth) (replay_1933 c1_depth r3_depth)
  have n1 : (shared_expr_Classification038_69 c1_depth r3_depth) := by
    exact Iff.mp (normalization_4790 c1_depth r3_depth) (replay_1934 c1_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4791 c1_depth r3_depth) hn

theorem normalized_1123 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ∧ (p4 ∧ (¬ p5)) ∧ p6) ∨ (((p3 ∧ (¬ p0)) ∨ (p2 ∧ (¬ p3))) ∧ (p7 ∧ (¬ p4)) ∧ (¬ (¬ p8)))) ↔ ((¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) ∨ (¬ p6))) ∨ (¬ ((¬ p8) ∨ (¬ p7) ∨ (¬ (¬ p4)) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ (¬ p0)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4792 (c1_node r3_node : Int) : (¬ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (not_congr (normalization_4611 c1_node r3_node))

abbrev shared_expr_Classification038_70 (c1_node c1_sign r3_node r3_sign : Int) : Prop := ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_4793 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1292 c1_node c1_sign r3_node r3_sign) ↔ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign) := (or_congr (normalization_1596 c1_sign) (or_congr (normalization_1598 c1_sign) (or_congr (normalization_2729 r3_sign) (normalization_4792 c1_node r3_node))))

theorem normalization_4794 (c1_node c1_sign r3_node r3_sign : Int) : (¬ (formula_1292 c1_node c1_sign r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign)) := (not_congr (normalization_4793 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Classification038_71 (c1_node c1_sign r3_node r3_sign : Int) : Prop := ((¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))))
theorem normalization_4795 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1293 c1_node c1_sign r3_node r3_sign) ↔ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign) := (or_congr (normalization_4613 c1_node r3_node) (or_congr (normalization_1622 c1_sign) (or_congr (normalization_1624 c1_sign) (normalization_2734 r3_sign))))

theorem normalization_4796 (c1_node c1_sign r3_node r3_sign : Int) : (¬ (formula_1293 c1_node c1_sign r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign)) := (not_congr (normalization_4795 c1_node c1_sign r3_node r3_sign))

theorem normalization_4797 (c1_node c1_sign r3_node r3_sign : Int) : ((¬ (formula_1292 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1293 c1_node c1_sign r3_node r3_sign))) ↔ ((¬ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign))) := (or_congr (normalization_4794 c1_node c1_sign r3_node r3_sign) (normalization_4796 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Classification038_72 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
abbrev shared_expr_Classification038_73 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification038_74 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((shared_expr_Classification038_72 c1_node c1_sign r3_node r3_sign) ∨ (shared_expr_Classification038_73 c1_node c1_sign r3_node r3_sign)) ↔ ((¬ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign))))
theorem normalization_4798 (c1_node c1_sign r3_node r3_sign : Int) : ((formula_1373 c1_node c1_sign r3_node r3_sign) ↔ ((¬ (formula_1292 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1293 c1_node c1_sign r3_node r3_sign)))) ↔ (shared_expr_Classification038_74 c1_node c1_sign r3_node r3_sign) := (iff_congr (normalization_4616 c1_node c1_sign r3_node r3_sign) (normalization_4797 c1_node c1_sign r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1936 (c1_node c1_sign r3_node r3_sign : Int) : ((formula_1373 c1_node c1_sign r3_node r3_sign) ↔ ((¬ (formula_1292 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1293 c1_node c1_sign r3_node r3_sign)))) := by
  classical
  have ht := (normalized_1123 ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)) ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((c1_sign) ≤ (1 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4798 c1_node c1_sign r3_node r3_sign) hn

abbrev shared_expr_Classification038_75 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))) ∧ ((¬ (formula_1292 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1293 c1_node c1_sign r3_node r3_sign))))
abbrev formula_1400 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_75 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)

theorem normalized_1124 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_76 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))) ∧ ((¬ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign))))
theorem normalization_4799 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : (formula_1400 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_76 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) := (and_congr (normalization_4789 c1_depth r3_depth) (normalization_4797 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Classification038_77 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification038_72 c1_node c1_sign r3_node r3_sign) ∨ (shared_expr_Classification038_73 c1_node c1_sign r3_node r3_sign)))
theorem normalization_4800 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : ((((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ (formula_1373 c1_node c1_sign r3_node r3_sign)) ↔ (formula_1400 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification038_77 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_76 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)) := (iff_congr (normalization_4617 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (normalization_4799 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1937 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : ((((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ (formula_1373 c1_node c1_sign r3_node r3_sign)) ↔ (formula_1400 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_1124 ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ((shared_expr_Classification038_72 c1_node c1_sign r3_node r3_sign) ∨ (shared_expr_Classification038_73 c1_node c1_sign r3_node r3_sign)) ((¬ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign))))
  have n0 : (shared_expr_Classification038_69 c1_depth r3_depth) := by
    exact Iff.mp (normalization_4791 c1_depth r3_depth) (replay_1935 c1_depth r3_depth)
  have n1 : (shared_expr_Classification038_74 c1_node c1_sign r3_node r3_sign) := by
    exact Iff.mp (normalization_4798 c1_node c1_sign r3_node r3_sign) (replay_1936 c1_node c1_sign r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4800 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) hn

theorem normalized_1125 (p0 p1 p2 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ p2) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4801 (c1_node c1_sign r3_node r3_sign : Int) : (¬ ((¬ (formula_1292 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1293 c1_node c1_sign r3_node r3_sign)))) ↔ (¬ ((¬ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign)))) := (not_congr (normalization_4797 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Classification038_78 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := ((¬ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∨ (¬ ((¬ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign)))))
theorem normalization_4802 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : (formula_1294 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) := (or_congr (normalization_4786 c1_depth r3_depth) (or_congr (normalization_4787 c1_depth r3_depth) (normalization_4801 c1_node c1_sign r3_node r3_sign)))

theorem normalization_4803 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : (¬ (formula_1294 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)) := (not_congr (normalization_4802 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))

theorem normalization_4804 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : ((formula_1400 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (¬ (formula_1294 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))) ↔ ((shared_expr_Classification038_76 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))) := (iff_congr (normalization_4799 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (normalization_4803 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1938 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : ((formula_1400 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (¬ (formula_1294 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))) := by
  classical
  have ht := (normalized_1125 ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((¬ (shared_expr_Classification038_70 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_71 c1_node c1_sign r3_node r3_sign))))
  have hn := ht
  exact Iff.mpr (normalization_4804 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) hn

theorem normalized_1126 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4805 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : ((((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ (formula_1373 c1_node c1_sign r3_node r3_sign)) ↔ (¬ (formula_1294 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))) ↔ ((shared_expr_Classification038_77 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))) := (iff_congr (normalization_4617 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (normalization_4803 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1939 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : ((((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ (formula_1373 c1_node c1_sign r3_node r3_sign)) ↔ (¬ (formula_1294 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))) := by
  classical
  have ht := (normalized_1126 (shared_expr_Classification038_77 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (shared_expr_Classification038_76 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))
  have n0 : ((shared_expr_Classification038_77 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (shared_expr_Classification038_76 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_4800 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (replay_1937 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification038_76 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_4804 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (replay_1938 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4805 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) hn

theorem normalized_1127 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5)) ∧ (p6 ↔ (¬ p7))) → ((p0 ∨ p2 ∨ p4 ∨ p6) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5) ∨ (¬ p7)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_79 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification038_64 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)))
theorem normalization_4806 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_599 r3_kind) (or_congr (normalization_1616 c1_kind) (or_congr (normalization_4779 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4803 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))))

abbrev shared_expr_Classification038_80 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ∨ (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (shared_expr_Classification038_77 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))
abbrev shared_expr_Classification038_81 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification038_80 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_4807 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1374 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) ↔ (shared_expr_Classification038_81 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (iff_congr (normalization_4618 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (normalization_4806 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1940 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1374 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) := by
  classical
  have ht := (normalized_1127 (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))) (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification038_58 c1_node c1_sign h r3_depth r3_node r3_sign)) (shared_expr_Classification038_64 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (shared_expr_Classification038_77 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))
  have n0 : ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2630 r3_kind) (replay_966 r3_kind)
  have n1 : ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1677 c1_kind) (replay_626 c1_kind)
  have n2 : (shared_expr_Classification038_66 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := by
    exact Iff.mp (normalization_4781 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (replay_1932 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)
  have n3 : ((shared_expr_Classification038_77 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification038_78 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_4805 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (replay_1939 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_4807 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

theorem normalized_1128 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_82 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_4808 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) ↔ (shared_expr_Classification038_82 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (iff_congr (normalization_4806 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (normalization_4806 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1941 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) := by
  classical
  have ht := (normalized_1128 (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_4808 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

theorem normalized_1129 (p0 p1 : Prop) : ((p0 ∧ (p1 ↔ p1)) → p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of trans.
theorem replay_1942 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1374 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) := by
  classical
  have ht := (normalized_1129 (shared_expr_Classification038_81 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
  have n0 : (shared_expr_Classification038_81 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
    exact Iff.mp (normalization_4807 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (replay_1940 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)
  have n1 : (shared_expr_Classification038_82 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
    exact Iff.mp (normalization_4808 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (replay_1941 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4807 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

abbrev shared_expr_Classification038_83 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∧ (formula_1059 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ∧ (formula_1295 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1401 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_83 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Classification038_84 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((formula_1375 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1401 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
abbrev formula_1402 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_84 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

theorem normalized_1130 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4809 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_4810 (c1_level r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := (not_congr (normalization_4809 c1_level r3_depth))

theorem normalization_4811 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) ≥ (-1 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_4812 (c1_level r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≥ (-1 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) := (not_congr (normalization_4811 c1_level r3_depth))

abbrev shared_expr_Classification038_85 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))))
theorem normalization_4813 (c1_level r3_depth r3_kind r3_sign : Int) : (formula_1047 c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Classification038_85 c1_level r3_depth r3_kind r3_sign) := (or_congr (normalization_2750 r3_kind) (or_congr (normalization_2752 r3_kind) (or_congr (normalization_2729 r3_sign) (or_congr (normalization_4810 c1_level r3_depth) (normalization_4812 c1_level r3_depth)))))

theorem normalization_4814 (c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1047 c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Classification038_85 c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_4813 c1_level r3_depth r3_kind r3_sign))

theorem normalization_4815 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4816 (c1_level r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_4815 c1_level r3_depth))

theorem normalization_4817 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4818 (c1_level r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (not_congr (normalization_4817 c1_level r3_depth))

abbrev shared_expr_Classification038_86 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_4819 (c1_level r3_depth r3_kind r3_sign : Int) : (formula_1048 c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Classification038_86 c1_level r3_depth r3_kind r3_sign) := (or_congr (normalization_2750 r3_kind) (or_congr (normalization_2752 r3_kind) (or_congr (normalization_2729 r3_sign) (or_congr (normalization_4816 c1_level r3_depth) (normalization_4818 c1_level r3_depth)))))

theorem normalization_4820 (c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1048 c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Classification038_86 c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_4819 c1_level r3_depth r3_kind r3_sign))

abbrev shared_expr_Classification038_87 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification038_85 c1_level r3_depth r3_kind r3_sign))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_86 c1_level r3_depth r3_kind r3_sign))))
theorem normalization_4821 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (formula_1049 c1_group c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Classification038_87 c1_group c1_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_1773 c1_group) (normalization_4814 c1_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_1773 c1_group)) (normalization_4820 c1_level r3_depth r3_kind r3_sign)))

theorem normalization_4822 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1049 c1_group c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Classification038_87 c1_group c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_4821 c1_group c1_level r3_depth r3_kind r3_sign))

theorem normalization_4823 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : ((¬ (c1_mode ≤ (0 : Int))) ∨ (¬ (c1_mode ≥ (0 : Int))) ∨ (¬ (formula_1049 c1_group c1_level r3_depth r3_kind r3_sign))) ↔ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification038_87 c1_group c1_level r3_depth r3_kind r3_sign))) := (or_congr (normalization_1766 c1_mode) (or_congr (normalization_1768 c1_mode) (normalization_4822 c1_group c1_level r3_depth r3_kind r3_sign)))

theorem normalization_4824 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (0 : Int))) ∨ (¬ (c1_mode ≥ (0 : Int))) ∨ (¬ (formula_1049 c1_group c1_level r3_depth r3_kind r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification038_87 c1_group c1_level r3_depth r3_kind r3_sign)))) := (not_congr (normalization_4823 c1_group c1_level c1_mode r3_depth r3_kind r3_sign))

abbrev shared_expr_Classification038_88 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_4825 (c1_level r3_depth r3_kind r3_sign : Int) : (formula_1050 c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Classification038_88 c1_level r3_depth r3_kind r3_sign) := (or_congr (normalization_2750 r3_kind) (or_congr (normalization_2752 r3_kind) (or_congr (normalization_2734 r3_sign) (or_congr (normalization_4816 c1_level r3_depth) (normalization_4818 c1_level r3_depth)))))

theorem normalization_4826 (c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1050 c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Classification038_88 c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_4825 c1_level r3_depth r3_kind r3_sign))

abbrev shared_expr_Classification038_89 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))))
theorem normalization_4827 (c1_level r3_depth r3_kind r3_sign : Int) : (formula_1051 c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Classification038_89 c1_level r3_depth r3_kind r3_sign) := (or_congr (normalization_2750 r3_kind) (or_congr (normalization_2752 r3_kind) (or_congr (normalization_2734 r3_sign) (or_congr (normalization_4810 c1_level r3_depth) (normalization_4812 c1_level r3_depth)))))

theorem normalization_4828 (c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1051 c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Classification038_89 c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_4827 c1_level r3_depth r3_kind r3_sign))

abbrev shared_expr_Classification038_90 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification038_88 c1_level r3_depth r3_kind r3_sign))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_89 c1_level r3_depth r3_kind r3_sign))))
theorem normalization_4829 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (formula_1052 c1_group c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Classification038_90 c1_group c1_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_1773 c1_group) (normalization_4826 c1_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_1773 c1_group)) (normalization_4828 c1_level r3_depth r3_kind r3_sign)))

theorem normalization_4830 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (¬ (formula_1052 c1_group c1_level r3_depth r3_kind r3_sign)) ↔ (¬ (shared_expr_Classification038_90 c1_group c1_level r3_depth r3_kind r3_sign)) := (not_congr (normalization_4829 c1_group c1_level r3_depth r3_kind r3_sign))

theorem normalization_4831 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : ((¬ (c1_mode ≤ (1 : Int))) ∨ (¬ (c1_mode ≥ (1 : Int))) ∨ (¬ (formula_1052 c1_group c1_level r3_depth r3_kind r3_sign))) ↔ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification038_90 c1_group c1_level r3_depth r3_kind r3_sign))) := (or_congr (normalization_1791 c1_mode) (or_congr (normalization_1793 c1_mode) (normalization_4830 c1_group c1_level r3_depth r3_kind r3_sign)))

theorem normalization_4832 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (1 : Int))) ∨ (¬ (c1_mode ≥ (1 : Int))) ∨ (¬ (formula_1052 c1_group c1_level r3_depth r3_kind r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification038_90 c1_group c1_level r3_depth r3_kind r3_sign)))) := (not_congr (normalization_4831 c1_group c1_level c1_mode r3_depth r3_kind r3_sign))

abbrev shared_expr_Classification038_91 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_4833 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1053 c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_91 c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_2750 r3_kind) (or_congr (normalization_2752 r3_kind) (or_congr (normalization_2729 r3_sign) (or_congr (normalization_2778 r3_node) (or_congr (normalization_4816 c1_level r3_depth) (normalization_4818 c1_level r3_depth))))))

theorem normalization_4834 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1053 c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_91 c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_4833 c1_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_92 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_91 c1_level r3_depth r3_kind r3_node r3_sign))))
theorem normalization_4835 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1054 c1_group c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_92 c1_group c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_1773 c1_group) (normalization_599 r3_kind)) (and_congr (not_congr (normalization_1773 c1_group)) (normalization_4834 c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_4836 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1054 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_92 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_4835 c1_group c1_level r3_depth r3_kind r3_node r3_sign))

theorem normalization_4837 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (c1_mode ≤ (2 : Int))) ∨ (¬ (c1_mode ≥ (2 : Int))) ∨ (¬ (formula_1054 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) ↔ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification038_92 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) := (or_congr (normalization_1803 c1_mode) (or_congr (normalization_1805 c1_mode) (normalization_4836 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_4838 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (2 : Int))) ∨ (¬ (c1_mode ≥ (2 : Int))) ∨ (¬ (formula_1054 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification038_92 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) := (not_congr (normalization_4837 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_93 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_4839 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1055 c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_93 c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_2750 r3_kind) (or_congr (normalization_2752 r3_kind) (or_congr (normalization_2729 r3_sign) (or_congr (normalization_2786 r3_node) (or_congr (normalization_4816 c1_level r3_depth) (normalization_4818 c1_level r3_depth))))))

theorem normalization_4840 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1055 c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_93 c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_4839 c1_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_94 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_93 c1_level r3_depth r3_kind r3_node r3_sign))))
theorem normalization_4841 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1056 c1_group c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_94 c1_group c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_1773 c1_group) (normalization_599 r3_kind)) (and_congr (not_congr (normalization_1773 c1_group)) (normalization_4840 c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_4842 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1056 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_94 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_4841 c1_group c1_level r3_depth r3_kind r3_node r3_sign))

theorem normalization_4843 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (c1_mode ≤ (3 : Int))) ∨ (¬ (c1_mode ≥ (3 : Int))) ∨ (¬ (formula_1056 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) ↔ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification038_94 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) := (or_congr (normalization_1813 c1_mode) (or_congr (normalization_1815 c1_mode) (normalization_4842 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_4844 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (3 : Int))) ∨ (¬ (c1_mode ≥ (3 : Int))) ∨ (¬ (formula_1056 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification038_94 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) := (not_congr (normalization_4843 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_95 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_4845 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1057 c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_95 c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_2750 r3_kind) (or_congr (normalization_2752 r3_kind) (or_congr (normalization_2734 r3_sign) (or_congr (normalization_2778 r3_node) (or_congr (normalization_4816 c1_level r3_depth) (normalization_4818 c1_level r3_depth))))))

theorem normalization_4846 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1057 c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_95 c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_4845 c1_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_96 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_95 c1_level r3_depth r3_kind r3_node r3_sign))))
theorem normalization_4847 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1058 c1_group c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_96 c1_group c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_1773 c1_group) (normalization_599 r3_kind)) (and_congr (not_congr (normalization_1773 c1_group)) (normalization_4846 c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_4848 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1058 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_96 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_4847 c1_group c1_level r3_depth r3_kind r3_node r3_sign))

theorem normalization_4849 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (c1_mode ≤ (4 : Int))) ∨ (¬ (c1_mode ≥ (4 : Int))) ∨ (¬ (formula_1058 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) ↔ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification038_96 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) := (or_congr (normalization_1823 c1_mode) (or_congr (normalization_1825 c1_mode) (normalization_4848 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_4850 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (4 : Int))) ∨ (¬ (c1_mode ≥ (4 : Int))) ∨ (¬ (formula_1058 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification038_96 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) := (not_congr (normalization_4849 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_97 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_4851 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1045 c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_97 c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_2750 r3_kind) (or_congr (normalization_2752 r3_kind) (or_congr (normalization_2734 r3_sign) (or_congr (normalization_2786 r3_node) (or_congr (normalization_4816 c1_level r3_depth) (normalization_4818 c1_level r3_depth))))))

theorem normalization_4852 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1045 c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_97 c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_4851 c1_level r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_98 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification038_97 c1_level r3_depth r3_kind r3_node r3_sign))))
theorem normalization_4853 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (formula_1046 c1_group c1_level r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_98 c1_group c1_level r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_1773 c1_group) (normalization_599 r3_kind)) (and_congr (not_congr (normalization_1773 c1_group)) (normalization_4852 c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_4854 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : (¬ (formula_1046 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ↔ (¬ (shared_expr_Classification038_98 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) := (not_congr (normalization_4853 c1_group c1_level r3_depth r3_kind r3_node r3_sign))

theorem normalization_4855 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((¬ (c1_mode ≤ (5 : Int))) ∨ (¬ (c1_mode ≥ (5 : Int))) ∨ (¬ (formula_1046 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) ↔ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification038_98 c1_group c1_level r3_depth r3_kind r3_node r3_sign))) := (or_congr (normalization_1833 c1_mode) (or_congr (normalization_1835 c1_mode) (normalization_4854 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))

theorem normalization_4856 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (¬ ((¬ (c1_mode ≤ (5 : Int))) ∨ (¬ (c1_mode ≥ (5 : Int))) ∨ (¬ (formula_1046 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification038_98 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) := (not_congr (normalization_4855 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_99 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification038_87 c1_group c1_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification038_90 c1_group c1_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification038_92 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification038_94 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification038_96 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification038_98 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))))
theorem normalization_4857 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (formula_1059 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_99 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_4824 c1_group c1_level c1_mode r3_depth r3_kind r3_sign) (or_congr (normalization_4832 c1_group c1_level c1_mode r3_depth r3_kind r3_sign) (or_congr (normalization_4838 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_4844 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_4850 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (normalization_4856 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))))))

abbrev shared_expr_Classification038_100 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_101 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_102 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_100 c1_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_101 c1_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Classification038_103 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_104 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_105 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_103 c1_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification038_104 c1_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Classification038_106 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification038_107 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_106 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_108 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification038_109 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_108 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_110 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification038_111 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_110 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_112 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification038_113 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_112 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification038_114 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_mode) ≤ (0 : Int)) ∧ (¬ ((c1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification038_102 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((((c1_mode) ≤ (1 : Int)) ∧ (¬ ((c1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification038_105 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((((c1_mode) ≤ (2 : Int)) ∧ (¬ ((c1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification038_107 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (3 : Int)) ∧ (¬ ((c1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification038_109 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (4 : Int)) ∧ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification038_111 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (5 : Int)) ∧ (¬ ((c1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification038_113 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))
theorem normalization_4858 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : ((formula_1371 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (formula_1059 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ↔ ((shared_expr_Classification038_114 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_99 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) := (iff_congr (normalization_4601 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (normalization_4857 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))

abbrev shared_expr_Classification038_115 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification038_99 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
theorem normalization_4859 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1401 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_115 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_1523 c1_kind) (normalization_4857 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) (and_congr (not_congr (normalization_1523 c1_kind)) (normalization_4806 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Classification038_116 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification038_114 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification038_80 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Classification038_117 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification038_116 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_115 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_4860 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1402 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_117 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (iff_congr (normalization_4619 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (normalization_4859 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1943 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1402 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
  classical
  have ht := (normalized_1130 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Classification038_114 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification038_99 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification038_80 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1525 c1_kind) (replay_591 c1_kind)
  have n1 : ((shared_expr_Classification038_114 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_99 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) := by
    exact Iff.mp (normalization_4858 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (replay_1910 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)
  have n2 : (shared_expr_Classification038_81 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
    exact Iff.mp (normalization_4807 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (replay_1942 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4860 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

abbrev shared_expr_Classification038_118 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((formula_1401 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1296 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
abbrev formula_1403 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_118 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

theorem normalized_1131 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_119 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification038_99 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)))
theorem normalization_4861 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1296 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_1522 c1_kind) (normalization_4806 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)) (and_congr (not_congr (normalization_1522 c1_kind)) (normalization_4857 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Classification038_120 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification038_115 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_4862 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1403 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_120 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (iff_congr (normalization_4859 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (normalization_4861 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1944 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1403 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
  classical
  have ht := (normalized_1131 ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Classification038_99 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification038_79 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_4862 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

abbrev shared_expr_Classification038_121 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((formula_1375 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1296 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
abbrev formula_1404 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_121 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

theorem normalized_1132 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_122 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification038_116 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_4863 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1404 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification038_122 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (iff_congr (normalization_4619 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (normalization_4861 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1945 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1404 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
  classical
  have ht := (normalized_1132 (shared_expr_Classification038_116 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification038_115 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification038_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
  have n0 : (shared_expr_Classification038_117 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
    exact Iff.mp (normalization_4860 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (replay_1943 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)
  have n1 : (shared_expr_Classification038_120 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
    exact Iff.mp (normalization_4862 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (replay_1944 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4863 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

abbrev shared_expr_Classification038_123 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((¬ ((¬ (r3_kind ≤ (0 : Int))) ∨ (¬ (r3_kind ≥ (0 : Int))))) ∧ (formula_1312 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) ∨ ((¬ (¬ ((¬ (r3_kind ≤ (0 : Int))) ∨ (¬ (r3_kind ≥ (0 : Int)))))) ∧ (formula_1296 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1405 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_123 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Classification038_124 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((formula_1376 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_1405 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_1406 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Classification038_124 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_1133 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification038_125 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ (¬ ((¬ ((r3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification038_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
abbrev shared_expr_Classification038_126 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((¬ ((¬ ((r3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification038_15 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) ∨ (shared_expr_Classification038_125 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_4864 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1405 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification038_126 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (and_congr (normalization_564 r3_kind) (normalization_4731 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_564 r3_kind)) (normalization_4861 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Classification038_127 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification038_33 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification038_116 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Classification038_128 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Classification038_127 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification038_126 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_4865 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1406 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification038_128 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_4620 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_4864 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1946 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1406 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_1133 (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ((¬ ((r3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (-1 : Int))))) (shared_expr_Classification038_33 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (shared_expr_Classification038_15 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (shared_expr_Classification038_116 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification038_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
  have n0 : ((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_566 r3_kind) (replay_139 r3_kind)
  have n1 : (shared_expr_Classification038_34 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_4733 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (replay_1909 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)
  have n2 : (shared_expr_Classification038_122 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
    exact Iff.mp (normalization_4863 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (replay_1945 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4865 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

end H4Formal.Generated.Classification
