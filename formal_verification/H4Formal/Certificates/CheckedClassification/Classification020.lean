import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification019

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Classification020_0 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_696 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (formula_625 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))
abbrev formula_698 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification020_0 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)

theorem normalized_593 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_1 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
abbrev shared_expr_Classification020_2 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification020_1 c2_depth c2_kind c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
abbrev shared_expr_Classification020_3 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
abbrev shared_expr_Classification020_4 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification020_3 c2_depth c2_kind c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
abbrev shared_expr_Classification020_5 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification020_6 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification020_5 c2_depth c2_kind c2_node c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification020_1 c2_depth c2_kind c2_sign r3_level))))
abbrev shared_expr_Classification020_7 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification020_8 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification020_7 c2_depth c2_kind c2_node c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification020_1 c2_depth c2_kind c2_sign r3_level))))
abbrev shared_expr_Classification020_9 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification020_10 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification020_3 c2_depth c2_kind c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification020_9 c2_depth c2_kind c2_node c2_sign r3_level))))
abbrev shared_expr_Classification020_11 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification020_12 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification020_3 c2_depth c2_kind c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification020_11 c2_depth c2_kind c2_node c2_sign r3_level))))
abbrev shared_expr_Classification020_13 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification020_2 c2_depth c2_kind c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification020_4 c2_depth c2_kind c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification020_6 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification020_8 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification020_10 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification020_12 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))))
abbrev shared_expr_Classification020_14 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
abbrev shared_expr_Classification020_15 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification020_13 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)) ∨ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification020_14 c2_group c2_level c2_mode r3_group r3_level r3_mode))))
theorem normalization_2624 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_625 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification020_15 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_889 c2_kind) (normalization_2620 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_889 c2_kind)) (normalization_2545 c2_group c2_level c2_mode r3_group r3_level r3_mode)))

abbrev shared_expr_Classification020_16 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification020_14 c2_group c2_level c2_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification020_13 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Classification020_17 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification020_16 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification020_15 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))
theorem normalization_2625 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_698 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification020_17 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := (iff_congr (normalization_2622 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) (normalization_2624 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_961 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_698 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_593 ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Classification020_14 c2_group c2_level c2_mode r3_group r3_level r3_mode) (shared_expr_Classification020_13 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))
  have hn := ht
  exact Iff.mpr (normalization_2625 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) hn

abbrev shared_expr_Classification020_18 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_681 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (formula_625 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))
abbrev formula_699 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification020_18 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)

theorem normalized_594 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_19 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
abbrev shared_expr_Classification020_20 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification020_21 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification020_20 c2_depth c2_kind c2_sign r3_level)))
abbrev shared_expr_Classification020_22 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification020_23 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification020_22 c2_depth c2_kind c2_sign r3_level)))
abbrev shared_expr_Classification020_24 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification020_25 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification020_20 c2_depth c2_kind c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification020_24 c2_depth c2_kind c2_node c2_sign r3_level)))
abbrev shared_expr_Classification020_26 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification020_27 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification020_20 c2_depth c2_kind c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification020_26 c2_depth c2_kind c2_node c2_sign r3_level)))
abbrev shared_expr_Classification020_28 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification020_29 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification020_28 c2_depth c2_kind c2_node c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification020_22 c2_depth c2_kind c2_sign r3_level)))
abbrev shared_expr_Classification020_30 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification020_31 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification020_30 c2_depth c2_kind c2_node c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification020_22 c2_depth c2_kind c2_sign r3_level)))
abbrev shared_expr_Classification020_32 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification020_21 c2_depth c2_kind c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification020_23 c2_depth c2_kind c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification020_25 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification020_27 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification020_29 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification020_31 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))
abbrev shared_expr_Classification020_33 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification020_19 c2_group c2_level c2_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification020_32 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Classification020_34 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification020_33 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification020_15 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))
theorem normalization_2626 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_699 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification020_34 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := (iff_congr (normalization_2456 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) (normalization_2624 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))

-- Checked replay of trans.
abbrev shared_expr_Classification020_35 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification020_33 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification020_16 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))
theorem replay_962 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_699 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_594 (shared_expr_Classification020_33 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) (shared_expr_Classification020_16 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) (shared_expr_Classification020_15 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))
  have n0 : (shared_expr_Classification020_35 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_2623 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) (replay_960 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)
  have n1 : (shared_expr_Classification020_17 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_2625 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) (replay_961 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2626 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_963 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : ((formula_684 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) ↔ (formula_214 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) := by
  classical
  first
  | (simp only [formula_684, formula_682, formula_683, formula_658, formula_659, formula_660, formula_661, formula_214, formula_205, formula_203, formula_204, formula_164, formula_162, formula_163, formula_207, formula_206, formula_209, formula_208, formula_211, formula_210, formula_213, formula_212, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_595 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2627 (r3_kind : Int) : ((r3_kind ≤ (2 : Int)) ∧ (r3_kind ≥ (2 : Int))) ↔ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) := (and_congr (normalization_594 r3_kind) (normalization_596 r3_kind))

theorem normalization_2628 (r3_kind : Int) : ((r3_kind = (2 : Int)) ↔ ((r3_kind ≤ (2 : Int)) ∧ (r3_kind ≥ (2 : Int)))) ↔ ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ↔ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))) := (iff_congr (normalization_469 r3_kind) (normalization_2627 r3_kind))

-- Checked replay of rewrite.
theorem replay_964 (r3_kind : Int) : ((r3_kind = (2 : Int)) ↔ ((r3_kind ≤ (2 : Int)) ∧ (r3_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_595 (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2628 r3_kind) hn

theorem normalized_596 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2629 (r3_kind : Int) : (((r3_kind ≤ (2 : Int)) ∧ (r3_kind ≥ (2 : Int))) ↔ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))))) ↔ ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_2627 r3_kind) (normalization_599 r3_kind))

-- Checked replay of rewrite.
theorem replay_965 (r3_kind : Int) : (((r3_kind ≤ (2 : Int)) ∧ (r3_kind ≥ (2 : Int))) ↔ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_596 ((r3_kind) ≤ (2 : Int)) ((r3_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2629 r3_kind) hn

theorem normalized_597 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2630 (r3_kind : Int) : ((r3_kind = (2 : Int)) ↔ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))))) ↔ ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_469 r3_kind) (normalization_599 r3_kind))

-- Checked replay of trans.
theorem replay_966 (r3_kind : Int) : ((r3_kind = (2 : Int)) ↔ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_597 (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))))
  have n0 : ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ↔ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_2628 r3_kind) (replay_964 r3_kind)
  have n1 : ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2629 r3_kind) (replay_965 r3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2630 r3_kind) hn

theorem normalized_598 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2631 (c2_depth r3_depth : Int) : (r3_depth ≤ c2_depth) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2632 (c2_depth r3_depth : Int) : (r3_depth ≥ c2_depth) ↔ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2633 (c2_depth r3_depth : Int) : ((r3_depth ≤ c2_depth) ∧ (r3_depth ≥ c2_depth)) ↔ ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (and_congr (normalization_2631 c2_depth r3_depth) (normalization_2632 c2_depth r3_depth))

abbrev shared_expr_Classification020_36 (c2_depth r3_depth : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_2634 (c2_depth r3_depth : Int) : ((r3_depth = c2_depth) ↔ ((r3_depth ≤ c2_depth) ∧ (r3_depth ≥ c2_depth))) ↔ (shared_expr_Classification020_36 c2_depth r3_depth) := (iff_congr (normalization_2351 c2_depth r3_depth) (normalization_2633 c2_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_967 (c2_depth r3_depth : Int) : ((r3_depth = c2_depth) ↔ ((r3_depth ≤ c2_depth) ∧ (r3_depth ≥ c2_depth))) := by
  classical
  have ht := (normalized_598 ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_2634 c2_depth r3_depth) hn

theorem normalized_599 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2635 (c2_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2636 (c2_depth r3_depth : Int) : ((r3_depth ≤ c2_depth) ↔ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_2631 c2_depth r3_depth) (normalization_2635 c2_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_968 (c2_depth r3_depth : Int) : ((r3_depth ≤ c2_depth) ↔ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_599 ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2636 c2_depth r3_depth) hn

theorem normalized_600 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2637 (c2_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2638 (c2_depth r3_depth : Int) : ((r3_depth ≥ c2_depth) ↔ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (iff_congr (normalization_2632 c2_depth r3_depth) (normalization_2637 c2_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_969 (c2_depth r3_depth : Int) : ((r3_depth ≥ c2_depth) ↔ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_600 ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2638 c2_depth r3_depth) hn

theorem normalized_601 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2639 (c2_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (and_congr (normalization_2635 c2_depth r3_depth) (normalization_2637 c2_depth r3_depth))

theorem normalization_2640 (c2_depth r3_depth : Int) : (((r3_depth ≤ c2_depth) ∧ (r3_depth ≥ c2_depth)) ↔ (((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification020_36 c2_depth r3_depth) := (iff_congr (normalization_2633 c2_depth r3_depth) (normalization_2639 c2_depth r3_depth))

-- Checked replay of monotonicity.
theorem replay_970 (c2_depth r3_depth : Int) : (((r3_depth ≤ c2_depth) ∧ (r3_depth ≥ c2_depth)) ↔ (((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_601 ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_2636 c2_depth r3_depth) (replay_968 c2_depth r3_depth)
  have n1 : (((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_2638 c2_depth r3_depth) (replay_969 c2_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2640 c2_depth r3_depth) hn

abbrev shared_expr_Classification020_37 (c2_depth r3_depth : Int) : Prop := ((((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))))
abbrev formula_700 (c2_depth r3_depth : Int) : Prop := (shared_expr_Classification020_37 c2_depth r3_depth)

theorem normalized_602 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2641 (c2_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2635 c2_depth r3_depth))

theorem normalization_2642 (c2_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (not_congr (normalization_2637 c2_depth r3_depth))

theorem normalization_2643 (c2_depth r3_depth : Int) : ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := (or_congr (normalization_2641 c2_depth r3_depth) (normalization_2642 c2_depth r3_depth))

theorem normalization_2644 (c2_depth r3_depth : Int) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))) := (not_congr (normalization_2643 c2_depth r3_depth))

abbrev shared_expr_Classification020_38 (c2_depth r3_depth : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))))
theorem normalization_2645 (c2_depth r3_depth : Int) : (formula_700 c2_depth r3_depth) ↔ (shared_expr_Classification020_38 c2_depth r3_depth) := (iff_congr (normalization_2639 c2_depth r3_depth) (normalization_2644 c2_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_971 (c2_depth r3_depth : Int) : (formula_700 c2_depth r3_depth) := by
  classical
  have ht := (normalized_602 ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2645 c2_depth r3_depth) hn

theorem normalized_603 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2646 (c2_depth r3_depth : Int) : (((r3_depth ≤ c2_depth) ∧ (r3_depth ≥ c2_depth)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification020_38 c2_depth r3_depth) := (iff_congr (normalization_2633 c2_depth r3_depth) (normalization_2644 c2_depth r3_depth))

-- Checked replay of trans.
theorem replay_972 (c2_depth r3_depth : Int) : (((r3_depth ≤ c2_depth) ∧ (r3_depth ≥ c2_depth)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_603 ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (shared_expr_Classification020_38 c2_depth r3_depth))
  have n0 : (shared_expr_Classification020_36 c2_depth r3_depth) := by
    exact Iff.mp (normalization_2640 c2_depth r3_depth) (replay_970 c2_depth r3_depth)
  have n1 : (shared_expr_Classification020_38 c2_depth r3_depth) := by
    exact Iff.mp (normalization_2645 c2_depth r3_depth) (replay_971 c2_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2646 c2_depth r3_depth) hn

theorem normalized_604 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2647 (c2_depth r3_depth : Int) : ((r3_depth = c2_depth) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification020_38 c2_depth r3_depth) := (iff_congr (normalization_2351 c2_depth r3_depth) (normalization_2644 c2_depth r3_depth))

-- Checked replay of trans.
theorem replay_973 (c2_depth r3_depth : Int) : ((r3_depth = c2_depth) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_604 ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (shared_expr_Classification020_38 c2_depth r3_depth))
  have n0 : (shared_expr_Classification020_36 c2_depth r3_depth) := by
    exact Iff.mp (normalization_2634 c2_depth r3_depth) (replay_967 c2_depth r3_depth)
  have n1 : (shared_expr_Classification020_38 c2_depth r3_depth) := by
    exact Iff.mp (normalization_2646 c2_depth r3_depth) (replay_972 c2_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2647 c2_depth r3_depth) hn

theorem normalized_605 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2648 (r3_sign : Int) : ((r3_sign ≤ (0 : Int)) ∧ (r3_sign ≥ (0 : Int))) ↔ (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) := (and_congr (normalization_617 r3_sign) (normalization_619 r3_sign))

theorem normalization_2649 (r3_sign : Int) : ((r3_sign = (0 : Int)) ↔ ((r3_sign ≤ (0 : Int)) ∧ (r3_sign ≥ (0 : Int)))) ↔ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int))))) := (iff_congr (normalization_472 r3_sign) (normalization_2648 r3_sign))

-- Checked replay of rewrite.
theorem replay_974 (r3_sign : Int) : ((r3_sign = (0 : Int)) ↔ ((r3_sign ≤ (0 : Int)) ∧ (r3_sign ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_605 (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2649 r3_sign) hn

theorem normalized_606 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2650 (r3_sign : Int) : (((r3_sign ≤ (0 : Int)) ∧ (r3_sign ≥ (0 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int)))))) ↔ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_2648 r3_sign) (normalization_622 r3_sign))

-- Checked replay of rewrite.
theorem replay_975 (r3_sign : Int) : (((r3_sign ≤ (0 : Int)) ∧ (r3_sign ≥ (0 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_606 ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2650 r3_sign) hn

theorem normalized_607 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2651 (r3_sign : Int) : ((r3_sign = (0 : Int)) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int)))))) ↔ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_472 r3_sign) (normalization_622 r3_sign))

-- Checked replay of trans.
theorem replay_976 (r3_sign : Int) : ((r3_sign = (0 : Int)) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_607 (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))))))
  have n0 : ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_2649 r3_sign) (replay_974 r3_sign)
  have n1 : ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_2650 r3_sign) (replay_975 r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2651 r3_sign) hn

abbrev shared_expr_Classification020_39 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((r3_sign = (0 : Int)) ∧ (c2_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev formula_701 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_39 c2_node c2_sign r3_node r3_sign)

theorem normalized_608 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2652 (c2_node c2_sign r3_node r3_sign : Int) : ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_622 r3_sign) (and_congr (normalization_976 c2_sign) (normalization_2465 c2_node r3_node)))

abbrev shared_expr_Classification020_40 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ↔ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))
theorem normalization_2653 (c2_node c2_sign r3_node r3_sign : Int) : (formula_701 c2_node c2_sign r3_node r3_sign) ↔ (shared_expr_Classification020_40 c2_node c2_sign r3_node r3_sign) := (iff_congr (normalization_2466 c2_node c2_sign r3_node r3_sign) (normalization_2652 c2_node c2_sign r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_977 (c2_node c2_sign r3_node r3_sign : Int) : (formula_701 c2_node c2_sign r3_node r3_sign) := by
  classical
  have ht := (normalized_608 (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))) (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))) ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have n0 : ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_2651 r3_sign) (replay_976 r3_sign)
  have n1 : ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1114 c2_sign) (replay_519 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2653 c2_node c2_sign r3_node r3_sign) hn

abbrev shared_expr_Classification020_41 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
abbrev formula_702 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_41 c2_node c2_sign r3_node r3_sign)

theorem normalized_609 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2654 (c2_node r3_node : Int) : (¬ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2465 c2_node r3_node))

theorem normalization_2655 (c2_node c2_sign r3_node r3_sign : Int) : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ↔ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_618 r3_sign) (or_congr (normalization_620 r3_sign) (or_congr (normalization_972 c2_sign) (or_congr (normalization_974 c2_sign) (normalization_2654 c2_node r3_node)))))

theorem normalization_2656 (c2_node c2_sign r3_node r3_sign : Int) : (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_2655 c2_node c2_sign r3_node r3_sign))

abbrev shared_expr_Classification020_42 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))))
theorem normalization_2657 (c2_node c2_sign r3_node r3_sign : Int) : (formula_702 c2_node c2_sign r3_node r3_sign) ↔ (shared_expr_Classification020_42 c2_node c2_sign r3_node r3_sign) := (iff_congr (normalization_2652 c2_node c2_sign r3_node r3_sign) (normalization_2656 c2_node c2_sign r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_978 (c2_node c2_sign r3_node r3_sign : Int) : (formula_702 c2_node c2_sign r3_node r3_sign) := by
  classical
  have ht := (normalized_609 ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2657 c2_node c2_sign r3_node r3_sign) hn

abbrev shared_expr_Classification020_43 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((r3_sign = (0 : Int)) ∧ (c2_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
abbrev formula_703 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_43 c2_node c2_sign r3_node r3_sign)

theorem normalized_610 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_44 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))))
theorem normalization_2658 (c2_node c2_sign r3_node r3_sign : Int) : (formula_703 c2_node c2_sign r3_node r3_sign) ↔ (shared_expr_Classification020_44 c2_node c2_sign r3_node r3_sign) := (iff_congr (normalization_2466 c2_node c2_sign r3_node r3_sign) (normalization_2656 c2_node c2_sign r3_node r3_sign))

-- Checked replay of trans.
theorem replay_979 (c2_node c2_sign r3_node r3_sign : Int) : (formula_703 c2_node c2_sign r3_node r3_sign) := by
  classical
  have ht := (normalized_610 ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))))
  have n0 : (shared_expr_Classification020_40 c2_node c2_sign r3_node r3_sign) := by
    exact Iff.mp (normalization_2653 c2_node c2_sign r3_node r3_sign) (replay_977 c2_node c2_sign r3_node r3_sign)
  have n1 : (shared_expr_Classification020_42 c2_node c2_sign r3_node r3_sign) := by
    exact Iff.mp (normalization_2657 c2_node c2_sign r3_node r3_sign) (replay_978 c2_node c2_sign r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2658 c2_node c2_sign r3_node r3_sign) hn

theorem normalized_611 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2659 (r3_sign : Int) : (r3_sign ≤ (2 : Int)) ↔ ((r3_sign) ≤ (2 : Int)) := by
  omega

theorem normalization_2660 (r3_sign : Int) : (r3_sign ≥ (2 : Int)) ↔ (¬ ((r3_sign) ≤ (1 : Int))) := by
  omega

theorem normalization_2661 (r3_sign : Int) : ((r3_sign ≤ (2 : Int)) ∧ (r3_sign ≥ (2 : Int))) ↔ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) := (and_congr (normalization_2659 r3_sign) (normalization_2660 r3_sign))

theorem normalization_2662 (r3_sign : Int) : ((r3_sign = (2 : Int)) ↔ ((r3_sign ≤ (2 : Int)) ∧ (r3_sign ≥ (2 : Int)))) ↔ ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ↔ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) := (iff_congr (normalization_2322 r3_sign) (normalization_2661 r3_sign))

-- Checked replay of rewrite.
theorem replay_980 (r3_sign : Int) : ((r3_sign = (2 : Int)) ↔ ((r3_sign ≤ (2 : Int)) ∧ (r3_sign ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_611 (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2662 r3_sign) hn

theorem normalized_612 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2663 (r3_sign : Int) : (¬ (r3_sign ≤ (2 : Int))) ↔ (¬ ((r3_sign) ≤ (2 : Int))) := (not_congr (normalization_2659 r3_sign))

theorem normalization_2664 (r3_sign : Int) : (¬ (r3_sign ≥ (2 : Int))) ↔ (¬ (¬ ((r3_sign) ≤ (1 : Int)))) := (not_congr (normalization_2660 r3_sign))

theorem normalization_2665 (r3_sign : Int) : ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))) ↔ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))) := (or_congr (normalization_2663 r3_sign) (normalization_2664 r3_sign))

theorem normalization_2666 (r3_sign : Int) : (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))) ↔ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))) := (not_congr (normalization_2665 r3_sign))

theorem normalization_2667 (r3_sign : Int) : (((r3_sign ≤ (2 : Int)) ∧ (r3_sign ≥ (2 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ↔ ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_2661 r3_sign) (normalization_2666 r3_sign))

-- Checked replay of rewrite.
theorem replay_981 (r3_sign : Int) : (((r3_sign ≤ (2 : Int)) ∧ (r3_sign ≥ (2 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_612 ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2667 r3_sign) hn

theorem normalized_613 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2668 (r3_sign : Int) : ((r3_sign = (2 : Int)) ↔ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ↔ ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_2322 r3_sign) (normalization_2666 r3_sign))

-- Checked replay of trans.
theorem replay_982 (r3_sign : Int) : ((r3_sign = (2 : Int)) ↔ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_613 (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))))
  have n0 : ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ↔ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_2662 r3_sign) (replay_980 r3_sign)
  have n1 : ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2667 r3_sign) (replay_981 r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2668 r3_sign) hn

theorem normalized_614 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2669 (h r3_depth : Int) : (r3_depth ≤ h) ↔ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2670 (h r3_depth : Int) : (r3_depth ≥ h) ↔ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2671 (h r3_depth : Int) : ((r3_depth ≤ h) ∧ (r3_depth ≥ h)) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (and_congr (normalization_2669 h r3_depth) (normalization_2670 h r3_depth))

theorem normalization_2672 (h r3_depth : Int) : ((r3_depth = h) ↔ ((r3_depth ≤ h) ∧ (r3_depth ≥ h))) ↔ (((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := (iff_congr (normalization_2357 h r3_depth) (normalization_2671 h r3_depth))

-- Checked replay of rewrite.
theorem replay_983 (h r3_depth : Int) : ((r3_depth = h) ↔ ((r3_depth ≤ h) ∧ (r3_depth ≥ h))) := by
  classical
  have ht := (normalized_614 ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_2672 h r3_depth) hn

theorem normalized_615 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2673 (h r3_depth : Int) : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) ↔ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2674 (h r3_depth : Int) : ((r3_depth ≤ h) ↔ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_2669 h r3_depth) (normalization_2673 h r3_depth))

-- Checked replay of rewrite.
theorem replay_984 (h r3_depth : Int) : ((r3_depth ≤ h) ↔ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_615 ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2674 h r3_depth) hn

theorem normalized_616 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2675 (h r3_depth : Int) : ((r3_depth ≥ h) ↔ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (iff_congr (normalization_2670 h r3_depth) (normalization_2468 h r3_depth))

-- Checked replay of rewrite.
theorem replay_985 (h r3_depth : Int) : ((r3_depth ≥ h) ↔ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_616 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2675 h r3_depth) hn

theorem normalized_617 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2676 (h r3_depth : Int) : (((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (and_congr (normalization_2673 h r3_depth) (normalization_2468 h r3_depth))

theorem normalization_2677 (h r3_depth : Int) : (((r3_depth ≤ h) ∧ (r3_depth ≥ h)) ↔ (((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) ↔ (((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := (iff_congr (normalization_2671 h r3_depth) (normalization_2676 h r3_depth))

-- Checked replay of monotonicity.
theorem replay_986 (h r3_depth : Int) : (((r3_depth ≤ h) ∧ (r3_depth ≥ h)) ↔ (((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := by
  classical
  have ht := (normalized_617 ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_2674 h r3_depth) (replay_984 h r3_depth)
  have n1 : (((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_2675 h r3_depth) (replay_985 h r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2677 h r3_depth) hn

theorem normalized_618 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ p1) ∨ (¬ (¬ p0))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2678 (h r3_depth : Int) : (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2673 h r3_depth))

theorem normalization_2679 (h r3_depth : Int) : ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_2469 h r3_depth) (normalization_2678 h r3_depth))

theorem normalization_2680 (h r3_depth : Int) : (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_2679 h r3_depth))

abbrev shared_expr_Classification020_45 (h r3_depth : Int) : Prop := (((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))))))
theorem normalization_2681 (h r3_depth : Int) : ((((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification020_45 h r3_depth) := (iff_congr (normalization_2676 h r3_depth) (normalization_2680 h r3_depth))

-- Checked replay of rewrite.
theorem replay_987 (h r3_depth : Int) : ((((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_618 ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2681 h r3_depth) hn

theorem normalized_619 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2682 (h r3_depth : Int) : (((r3_depth ≤ h) ∧ (r3_depth ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification020_45 h r3_depth) := (iff_congr (normalization_2671 h r3_depth) (normalization_2680 h r3_depth))

-- Checked replay of trans.
theorem replay_988 (h r3_depth : Int) : (((r3_depth ≤ h) ∧ (r3_depth ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_619 ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (shared_expr_Classification020_45 h r3_depth))
  have n0 : (((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := by
    exact Iff.mp (normalization_2677 h r3_depth) (replay_986 h r3_depth)
  have n1 : (shared_expr_Classification020_45 h r3_depth) := by
    exact Iff.mp (normalization_2681 h r3_depth) (replay_987 h r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2682 h r3_depth) hn

theorem normalized_620 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2683 (h r3_depth : Int) : ((r3_depth = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification020_45 h r3_depth) := (iff_congr (normalization_2357 h r3_depth) (normalization_2680 h r3_depth))

-- Checked replay of trans.
theorem replay_989 (h r3_depth : Int) : ((r3_depth = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_620 ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (shared_expr_Classification020_45 h r3_depth))
  have n0 : (((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := by
    exact Iff.mp (normalization_2672 h r3_depth) (replay_983 h r3_depth)
  have n1 : (shared_expr_Classification020_45 h r3_depth) := by
    exact Iff.mp (normalization_2682 h r3_depth) (replay_988 h r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2683 h r3_depth) hn

abbrev shared_expr_Classification020_46 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
abbrev formula_704 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_46 c2_node c2_sign h r3_depth r3_node r3_sign)

theorem normalized_621 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∧ p2 ∧ p4 ∧ (¬ p6)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p5) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_47 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
theorem normalization_2684 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_704 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_47 c2_node c2_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2666 r3_sign) (and_congr (normalization_982 c2_sign) (and_congr (normalization_2680 h r3_depth) (normalization_2465 c2_node r3_node))))

abbrev shared_expr_Classification020_48 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ∧ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
theorem normalization_2685 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (((r3_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (formula_704 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification020_48 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_47 c2_node c2_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_2467 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2684 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_990 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (((r3_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (formula_704 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_621 (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))) (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int)))) ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))) ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))) ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have n0 : ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2668 r3_sign) (replay_982 r3_sign)
  have n1 : ((((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1135 c2_sign) (replay_528 c2_sign)
  have n2 : (shared_expr_Classification020_45 h r3_depth) := by
    exact Iff.mp (normalization_2683 h r3_depth) (replay_989 h r3_depth)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2685 c2_node c2_sign h r3_depth r3_node r3_sign) hn

theorem normalized_622 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ ((¬ p4) ∨ (¬ (¬ p5)))) ∧ (¬ p6)) ↔ (¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p6))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_49 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))) ∨ (¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))
theorem normalization_2686 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_602 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2469 h r3_depth) (or_congr (normalization_2678 h r3_depth) (or_congr (normalization_2663 r3_sign) (or_congr (normalization_2664 r3_sign) (or_congr (normalization_978 c2_sign) (or_congr (normalization_980 c2_sign) (normalization_2654 c2_node r3_node)))))))

theorem normalization_2687 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_602 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_2686 c2_node c2_sign h r3_depth r3_node r3_sign))

theorem normalization_2688 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_704 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (formula_602 c2_node c2_sign h r3_depth r3_node r3_sign))) ↔ ((shared_expr_Classification020_47 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_2684 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2687 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_991 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_704 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (formula_602 c2_node c2_sign h r3_depth r3_node r3_sign))) := by
  classical
  have ht := (normalized_622 ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)) ((c2_sign) ≤ (2 : Int)) ((c2_sign) ≤ (1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2688 c2_node c2_sign h r3_depth r3_node r3_sign) hn

theorem normalized_623 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2689 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (((r3_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ (formula_602 c2_node c2_sign h r3_depth r3_node r3_sign))) ↔ ((shared_expr_Classification020_48 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_2467 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2687 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_992 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (((r3_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ (formula_602 c2_node c2_sign h r3_depth r3_node r3_sign))) := by
  classical
  have ht := (normalized_623 (shared_expr_Classification020_48 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_47 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign))
  have n0 : ((shared_expr_Classification020_48 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_47 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_2685 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_990 c2_node c2_sign h r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification020_47 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_2688 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_991 c2_node c2_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2689 c2_node c2_sign h r3_depth r3_node r3_sign) hn

theorem normalized_624 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2690 (r3_sign : Int) : (r3_sign ≤ (1 : Int)) ↔ ((r3_sign) ≤ (1 : Int)) := by
  omega

theorem normalization_2691 (r3_sign : Int) : (r3_sign ≥ (1 : Int)) ↔ (¬ ((r3_sign) ≤ (0 : Int))) := by
  omega

theorem normalization_2692 (r3_sign : Int) : ((r3_sign ≤ (1 : Int)) ∧ (r3_sign ≥ (1 : Int))) ↔ (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) := (and_congr (normalization_2690 r3_sign) (normalization_2691 r3_sign))

theorem normalization_2693 (r3_sign : Int) : ((r3_sign = (1 : Int)) ↔ ((r3_sign ≤ (1 : Int)) ∧ (r3_sign ≥ (1 : Int)))) ↔ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ↔ (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int))))) := (iff_congr (normalization_2329 r3_sign) (normalization_2692 r3_sign))

-- Checked replay of rewrite.
theorem replay_993 (r3_sign : Int) : ((r3_sign = (1 : Int)) ↔ ((r3_sign ≤ (1 : Int)) ∧ (r3_sign ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_624 (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2693 r3_sign) hn

theorem normalized_625 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2694 (r3_sign : Int) : (¬ (r3_sign ≤ (1 : Int))) ↔ (¬ ((r3_sign) ≤ (1 : Int))) := (not_congr (normalization_2690 r3_sign))

theorem normalization_2695 (r3_sign : Int) : (¬ (r3_sign ≥ (1 : Int))) ↔ (¬ (¬ ((r3_sign) ≤ (0 : Int)))) := (not_congr (normalization_2691 r3_sign))

theorem normalization_2696 (r3_sign : Int) : ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) ↔ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))) := (or_congr (normalization_2694 r3_sign) (normalization_2695 r3_sign))

theorem normalization_2697 (r3_sign : Int) : (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_2696 r3_sign))

theorem normalization_2698 (r3_sign : Int) : (((r3_sign ≤ (1 : Int)) ∧ (r3_sign ≥ (1 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))))) ↔ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_2692 r3_sign) (normalization_2697 r3_sign))

-- Checked replay of rewrite.
theorem replay_994 (r3_sign : Int) : (((r3_sign ≤ (1 : Int)) ∧ (r3_sign ≥ (1 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_625 ((r3_sign) ≤ (1 : Int)) ((r3_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2698 r3_sign) hn

theorem normalized_626 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2699 (r3_sign : Int) : ((r3_sign = (1 : Int)) ↔ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))))) ↔ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_2329 r3_sign) (normalization_2697 r3_sign))

-- Checked replay of trans.
theorem replay_995 (r3_sign : Int) : ((r3_sign = (1 : Int)) ↔ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_626 (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))))))
  have n0 : ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ↔ (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_2693 r3_sign) (replay_993 r3_sign)
  have n1 : ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_2698 r3_sign) (replay_994 r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2699 r3_sign) hn

abbrev shared_expr_Classification020_50 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))
abbrev formula_705 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_50 c2_node c2_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Classification020_51 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_sign = (1 : Int)) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (formula_705 c2_node c2_sign h r3_depth r3_node r3_sign))
abbrev formula_706 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_51 c2_node c2_sign h r3_depth r3_node r3_sign)

theorem normalized_627 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4) ∧ (¬ p5)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4) ∧ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_52 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
theorem normalization_2700 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_705 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_52 c2_node c2_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2697 r3_sign) (and_congr (normalization_1006 c2_sign) (and_congr (normalization_2469 h r3_depth) (normalization_2471 c2_node r3_node))))

abbrev shared_expr_Classification020_53 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
theorem normalization_2701 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_706 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ ((shared_expr_Classification020_53 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_52 c2_node c2_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_2472 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2700 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_996 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_706 c2_node c2_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_627 (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))) (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)))
  have n0 : ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_2699 r3_sign) (replay_995 r3_sign)
  have n1 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1170 c2_sign) (replay_544 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2701 c2_node c2_sign h r3_depth r3_node r3_sign) hn

theorem normalized_628 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4) ∧ (¬ p5)) ↔ (¬ (p4 ∨ p5 ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_54 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ∨ ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ∨ (¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))
theorem normalization_2702 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_603 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2468 h r3_depth) (or_congr (normalization_2470 c2_node r3_node) (or_congr (normalization_2694 r3_sign) (or_congr (normalization_2695 r3_sign) (or_congr (normalization_1002 c2_sign) (normalization_1004 c2_sign))))))

theorem normalization_2703 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_603 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_2702 c2_node c2_sign h r3_depth r3_node r3_sign))

theorem normalization_2704 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_705 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (formula_603 c2_node c2_sign h r3_depth r3_node r3_sign))) ↔ ((shared_expr_Classification020_52 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_2700 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2703 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_997 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_705 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (formula_603 c2_node c2_sign h r3_depth r3_node r3_sign))) := by
  classical
  have ht := (normalized_628 ((r3_sign) ≤ (1 : Int)) ((r3_sign) ≤ (0 : Int)) ((c2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2704 c2_node c2_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification020_55 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_sign = (1 : Int)) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (¬ (formula_603 c2_node c2_sign h r3_depth r3_node r3_sign)))
abbrev formula_707 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_55 c2_node c2_sign h r3_depth r3_node r3_sign)

theorem normalized_629 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2705 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_707 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ ((shared_expr_Classification020_53 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_2472 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2703 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_998 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_707 c2_node c2_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_629 (shared_expr_Classification020_53 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_52 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign))
  have n0 : ((shared_expr_Classification020_53 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_52 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_2701 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_996 c2_node c2_sign h r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification020_52 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_2704 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_997 c2_node c2_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2705 c2_node c2_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification020_56 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ∨ (¬ (formula_602 c2_node c2_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_603 c2_node c2_sign h r3_depth r3_node r3_sign)))
abbrev formula_708 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_56 c2_node c2_sign h r3_depth r3_node r3_sign)

theorem normalized_630 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∨ p2 ∨ p4) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_57 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign)) ∨ (¬ (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign)))
theorem normalization_2706 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_708 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_57 c2_node c2_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2656 c2_node c2_sign r3_node r3_sign) (or_congr (normalization_2687 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2703 c2_node c2_sign h r3_depth r3_node r3_sign)))

abbrev shared_expr_Classification020_58 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification020_48 c2_node c2_sign h r3_depth r3_node r3_sign) ∨ (shared_expr_Classification020_53 c2_node c2_sign h r3_depth r3_node r3_sign))
theorem normalization_2707 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_685 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (formula_708 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_57 c2_node c2_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_2473 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2706 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_999 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_685 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (formula_708 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_630 ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))) (shared_expr_Classification020_48 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_53 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign))
  have n0 : (shared_expr_Classification020_44 c2_node c2_sign r3_node r3_sign) := by
    exact Iff.mp (normalization_2658 c2_node c2_sign r3_node r3_sign) (replay_979 c2_node c2_sign r3_node r3_sign)
  have n1 : ((shared_expr_Classification020_48 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_2689 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_992 c2_node c2_sign h r3_depth r3_node r3_sign)
  have n2 : ((shared_expr_Classification020_53 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_2705 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_998 c2_node c2_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2707 c2_node c2_sign h r3_depth r3_node r3_sign) hn

theorem normalized_631 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ↔ ((¬ p1) ∨ (¬ p0) ∨ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_59 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign)))
theorem normalization_2708 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2687 c2_node c2_sign h r3_depth r3_node r3_sign) (or_congr (normalization_2656 c2_node c2_sign r3_node r3_sign) (normalization_2703 c2_node c2_sign h r3_depth r3_node r3_sign)))

theorem normalization_2709 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_708 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification020_57 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_2706 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2708 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1000 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_708 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_631 ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))) (shared_expr_Classification020_49 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_54 c2_node c2_sign h r3_depth r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_2709 c2_node c2_sign h r3_depth r3_node r3_sign) hn

theorem normalized_632 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2710 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_685 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ ((shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign)) := (iff_congr (normalization_2473 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2708 c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1001 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_685 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
  classical
  have ht := (normalized_632 (shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_57 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign))
  have n0 : ((shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_57 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_2707 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_999 c2_node c2_sign h r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification020_57 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_2709 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_1000 c2_node c2_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2710 c2_node c2_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification020_60 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_depth = c2_depth) ∧ (formula_685 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ ((¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)))
abbrev formula_709 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_60 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign)

theorem normalized_633 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_61 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))) ∧ (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign))
theorem normalization_2711 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (shared_expr_Classification020_61 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2644 c2_depth r3_depth) (normalization_2708 c2_node c2_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Classification020_62 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (shared_expr_Classification020_61 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))
theorem normalization_2712 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_709 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_62 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := (iff_congr (normalization_2474 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2711 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1002 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_709 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_633 ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) (shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign))
  have n0 : (shared_expr_Classification020_38 c2_depth r3_depth) := by
    exact Iff.mp (normalization_2647 c2_depth r3_depth) (replay_973 c2_depth r3_depth)
  have n1 : ((shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign)) := by
    exact Iff.mp (normalization_2710 c2_node c2_sign h r3_depth r3_node r3_sign) (replay_1001 c2_node c2_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2712 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification020_63 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)))))
abbrev formula_710 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_63 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign)

theorem normalized_634 (p0 p1 p2 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ p2) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2713 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (¬ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_2708 c2_node c2_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Classification020_64 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign)))
theorem normalization_2714 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign))) ↔ (shared_expr_Classification020_64 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_2641 c2_depth r3_depth) (or_congr (normalization_2642 c2_depth r3_depth) (normalization_2713 c2_node c2_sign h r3_depth r3_node r3_sign)))

theorem normalization_2715 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)))) ↔ (¬ (shared_expr_Classification020_64 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign)) := (not_congr (normalization_2714 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))

theorem normalization_2716 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_710 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) ↔ ((shared_expr_Classification020_61 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_64 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))) := (iff_congr (normalization_2711 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2715 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1003 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_710 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_634 ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) (shared_expr_Classification020_59 c2_node c2_sign h r3_depth r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_2716 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) hn

abbrev shared_expr_Classification020_65 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_depth = c2_depth) ∧ (formula_685 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_604 c2_node c2_sign h r3_depth r3_node r3_sign)))))
abbrev formula_711 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification020_65 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign)

theorem normalized_635 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification020_66 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (¬ (shared_expr_Classification020_64 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign)))
theorem normalization_2717 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_711 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification020_66 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := (iff_congr (normalization_2474 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_2715 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))

-- Checked replay of trans.
theorem replay_1004 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_711 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := by
  classical
  have ht := (normalized_635 (((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification020_58 c2_node c2_sign h r3_depth r3_node r3_sign)) (shared_expr_Classification020_61 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (shared_expr_Classification020_64 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))
  have n0 : (shared_expr_Classification020_62 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := by
    exact Iff.mp (normalization_2712 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (replay_1002 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign)
  have n1 : ((shared_expr_Classification020_61 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (¬ (shared_expr_Classification020_64 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))) := by
    exact Iff.mp (normalization_2716 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (replay_1003 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2717 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) hn

theorem normalized_636 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2718 (c2_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_2719 (c2_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ↔ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2720 (c2_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := (and_congr (normalization_2718 c2_depth r3_depth) (normalization_2719 c2_depth r3_depth))

abbrev shared_expr_Classification020_67 (c2_depth r3_depth : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))
theorem normalization_2721 (c2_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification020_67 c2_depth r3_depth) := (iff_congr (normalization_2475 c2_depth r3_depth) (normalization_2720 c2_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_1005 (c2_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_636 ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_2721 c2_depth r3_depth) hn

abbrev shared_expr_Classification020_68 (c2_depth r3_depth : Int) : Prop := ((((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))
abbrev formula_712 (c2_depth r3_depth : Int) : Prop := (shared_expr_Classification020_68 c2_depth r3_depth)

theorem normalized_637 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2722 (c2_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_2718 c2_depth r3_depth))

theorem normalization_2723 (c2_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := (not_congr (normalization_2719 c2_depth r3_depth))

theorem normalization_2724 (c2_depth r3_depth : Int) : ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (or_congr (normalization_2722 c2_depth r3_depth) (normalization_2723 c2_depth r3_depth))

theorem normalization_2725 (c2_depth r3_depth : Int) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))) := (not_congr (normalization_2724 c2_depth r3_depth))

abbrev shared_expr_Classification020_69 (c2_depth r3_depth : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))))))
theorem normalization_2726 (c2_depth r3_depth : Int) : (formula_712 c2_depth r3_depth) ↔ (shared_expr_Classification020_69 c2_depth r3_depth) := (iff_congr (normalization_2720 c2_depth r3_depth) (normalization_2725 c2_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_1006 (c2_depth r3_depth : Int) : (formula_712 c2_depth r3_depth) := by
  classical
  have ht := (normalized_637 ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)) ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2726 c2_depth r3_depth) hn

theorem normalized_638 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2727 (c2_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification020_69 c2_depth r3_depth) := (iff_congr (normalization_2475 c2_depth r3_depth) (normalization_2725 c2_depth r3_depth))

-- Checked replay of trans.
theorem replay_1007 (c2_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_638 ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) (shared_expr_Classification020_69 c2_depth r3_depth))
  have n0 : (shared_expr_Classification020_67 c2_depth r3_depth) := by
    exact Iff.mp (normalization_2721 c2_depth r3_depth) (replay_1005 c2_depth r3_depth)
  have n1 : (shared_expr_Classification020_69 c2_depth r3_depth) := by
    exact Iff.mp (normalization_2726 c2_depth r3_depth) (replay_1006 c2_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2727 c2_depth r3_depth) hn

theorem normalized_639 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ∧ (p4 ∧ (¬ p5)) ∧ p6) ∨ (((p3 ∧ (¬ p0)) ∨ (p2 ∧ (¬ p3))) ∧ (p7 ∧ (¬ p4)) ∧ (¬ (¬ p8)))) ↔ ((¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) ∨ (¬ p6))) ∨ (¬ ((¬ p8) ∨ (¬ p7) ∨ (¬ (¬ p4)) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ (¬ p0)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2728 (r3_sign : Int) : ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))) := (or_congr (normalization_622 r3_sign) (normalization_2666 r3_sign))

theorem normalization_2729 (r3_sign : Int) : (¬ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_2728 r3_sign))

theorem normalization_2730 (c2_node r3_node : Int) : (¬ ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_2476 c2_node r3_node))

abbrev shared_expr_Classification020_70 (c2_node c2_sign r3_node r3_sign : Int) : Prop := ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) ∨ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_2731 (c2_node c2_sign r3_node r3_sign : Int) : (formula_605 c2_node c2_sign r3_node r3_sign) ↔ (shared_expr_Classification020_70 c2_node c2_sign r3_node r3_sign) := (or_congr (normalization_972 c2_sign) (or_congr (normalization_974 c2_sign) (or_congr (normalization_2729 r3_sign) (normalization_2730 c2_node r3_node))))

theorem normalization_2732 (c2_node c2_sign r3_node r3_sign : Int) : (¬ (formula_605 c2_node c2_sign r3_node r3_sign)) ↔ (¬ (shared_expr_Classification020_70 c2_node c2_sign r3_node r3_sign)) := (not_congr (normalization_2731 c2_node c2_sign r3_node r3_sign))

theorem normalization_2733 (r3_sign : Int) : ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int))))))) := (or_congr (normalization_2697 r3_sign) (normalization_2666 r3_sign))

theorem normalization_2734 (r3_sign : Int) : (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_2733 r3_sign))

abbrev shared_expr_Classification020_71 (c2_node c2_sign r3_node r3_sign : Int) : Prop := ((¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (1 : Int)))))))))
theorem normalization_2735 (c2_node c2_sign r3_node r3_sign : Int) : (formula_606 c2_node c2_sign r3_node r3_sign) ↔ (shared_expr_Classification020_71 c2_node c2_sign r3_node r3_sign) := (or_congr (normalization_2478 c2_node r3_node) (or_congr (normalization_1002 c2_sign) (or_congr (normalization_1004 c2_sign) (normalization_2734 r3_sign))))

theorem normalization_2736 (c2_node c2_sign r3_node r3_sign : Int) : (¬ (formula_606 c2_node c2_sign r3_node r3_sign)) ↔ (¬ (shared_expr_Classification020_71 c2_node c2_sign r3_node r3_sign)) := (not_congr (normalization_2735 c2_node c2_sign r3_node r3_sign))

theorem normalization_2737 (c2_node c2_sign r3_node r3_sign : Int) : ((¬ (formula_605 c2_node c2_sign r3_node r3_sign)) ∨ (¬ (formula_606 c2_node c2_sign r3_node r3_sign))) ↔ ((¬ (shared_expr_Classification020_70 c2_node c2_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification020_71 c2_node c2_sign r3_node r3_sign))) := (or_congr (normalization_2732 c2_node c2_sign r3_node r3_sign) (normalization_2736 c2_node c2_sign r3_node r3_sign))

abbrev shared_expr_Classification020_72 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
abbrev shared_expr_Classification020_73 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification020_74 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((shared_expr_Classification020_72 c2_node c2_sign r3_node r3_sign) ∨ (shared_expr_Classification020_73 c2_node c2_sign r3_node r3_sign)) ↔ ((¬ (shared_expr_Classification020_70 c2_node c2_sign r3_node r3_sign)) ∨ (¬ (shared_expr_Classification020_71 c2_node c2_sign r3_node r3_sign))))
theorem normalization_2738 (c2_node c2_sign r3_node r3_sign : Int) : ((formula_686 c2_node c2_sign r3_node r3_sign) ↔ ((¬ (formula_605 c2_node c2_sign r3_node r3_sign)) ∨ (¬ (formula_606 c2_node c2_sign r3_node r3_sign)))) ↔ (shared_expr_Classification020_74 c2_node c2_sign r3_node r3_sign) := (iff_congr (normalization_2481 c2_node c2_sign r3_node r3_sign) (normalization_2737 c2_node c2_sign r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1008 (c2_node c2_sign r3_node r3_sign : Int) : ((formula_686 c2_node c2_sign r3_node r3_sign) ↔ ((¬ (formula_605 c2_node c2_sign r3_node r3_sign)) ∨ (¬ (formula_606 c2_node c2_sign r3_node r3_sign)))) := by
  classical
  have ht := (normalized_639 ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c2_sign) ≤ (1 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2738 c2_node c2_sign r3_node r3_sign) hn

end H4Formal.Generated.Classification
