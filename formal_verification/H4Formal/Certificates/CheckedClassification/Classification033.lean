import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification032

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Classification033_0 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((formula_1255 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (formula_1184 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))
abbrev formula_1257 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification033_0 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)

theorem normalized_963 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_1 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))
abbrev shared_expr_Classification033_2 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification033_1 c2_depth c2_kind c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
abbrev shared_expr_Classification033_3 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))
abbrev shared_expr_Classification033_4 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification033_3 c2_depth c2_kind c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
abbrev shared_expr_Classification033_5 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification033_6 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification033_5 c2_depth c2_kind c2_node c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification033_1 c2_depth c2_kind c2_sign r2_level))))
abbrev shared_expr_Classification033_7 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification033_8 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification033_7 c2_depth c2_kind c2_node c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification033_1 c2_depth c2_kind c2_sign r2_level))))
abbrev shared_expr_Classification033_9 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification033_10 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification033_3 c2_depth c2_kind c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification033_9 c2_depth c2_kind c2_node c2_sign r2_level))))
abbrev shared_expr_Classification033_11 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification033_12 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification033_3 c2_depth c2_kind c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification033_11 c2_depth c2_kind c2_node c2_sign r2_level))))
abbrev shared_expr_Classification033_13 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ ((r2_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification033_2 c2_depth c2_kind c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification033_4 c2_depth c2_kind c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification033_6 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification033_8 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification033_10 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification033_12 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))))
abbrev shared_expr_Classification033_14 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))))
abbrev shared_expr_Classification033_15 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification033_13 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) ∨ ((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification033_14 c2_group c2_level c2_mode r2_group r2_level r2_mode))))
theorem normalization_4271 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1184 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification033_15 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_889 c2_kind) (normalization_4267 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_889 c2_kind)) (normalization_4201 c2_group c2_level c2_mode r2_group r2_level r2_mode)))

abbrev shared_expr_Classification033_16 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification033_14 c2_group c2_level c2_mode r2_group r2_level r2_mode))) ∨ ((¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification033_13 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))
abbrev shared_expr_Classification033_17 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Classification033_16 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification033_15 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))
theorem normalization_4272 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1257 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification033_17 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := (iff_congr (normalization_4269 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) (normalization_4271 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))

-- Checked replay of rewrite.
theorem replay_1616 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1257 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := by
  classical
  have ht := (normalized_963 ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Classification033_14 c2_group c2_level c2_mode r2_group r2_level r2_mode) (shared_expr_Classification033_13 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))
  have hn := ht
  exact Iff.mpr (normalization_4272 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) hn

abbrev shared_expr_Classification033_18 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((formula_1240 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (formula_1184 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))
abbrev formula_1258 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification033_18 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)

theorem normalized_964 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_19 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
abbrev shared_expr_Classification033_20 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification033_21 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification033_20 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification033_22 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification033_23 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification033_22 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification033_24 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification033_25 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification033_20 c2_depth c2_kind c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification033_24 c2_depth c2_kind c2_node c2_sign r2_level)))
abbrev shared_expr_Classification033_26 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification033_27 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification033_20 c2_depth c2_kind c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification033_26 c2_depth c2_kind c2_node c2_sign r2_level)))
abbrev shared_expr_Classification033_28 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification033_29 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification033_28 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification033_22 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification033_30 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification033_31 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification033_30 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification033_22 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification033_32 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((((r2_mode) ≤ (0 : Int)) ∧ (¬ ((r2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification033_21 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (1 : Int)) ∧ (¬ ((r2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification033_23 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (2 : Int)) ∧ (¬ ((r2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification033_25 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (3 : Int)) ∧ (¬ ((r2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification033_27 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (4 : Int)) ∧ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification033_29 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (5 : Int)) ∧ (¬ ((r2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification033_31 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))
abbrev shared_expr_Classification033_33 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification033_19 c2_group c2_level c2_mode r2_group r2_level r2_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification033_32 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))
abbrev shared_expr_Classification033_34 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Classification033_33 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification033_15 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))
theorem normalization_4273 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1258 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification033_34 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := (iff_congr (normalization_4114 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) (normalization_4271 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))

-- Checked replay of trans.
abbrev shared_expr_Classification033_35 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Classification033_33 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification033_16 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))
theorem replay_1617 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1258 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := by
  classical
  have ht := (normalized_964 (shared_expr_Classification033_33 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) (shared_expr_Classification033_16 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) (shared_expr_Classification033_15 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))
  have n0 : (shared_expr_Classification033_35 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := by
    exact Iff.mp (normalization_4270 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) (replay_1615 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)
  have n1 : (shared_expr_Classification033_17 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := by
    exact Iff.mp (normalization_4272 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) (replay_1616 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4273 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) hn

-- Checked replay of rewrite.
theorem replay_1618 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : ((formula_1243 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) ↔ (formula_179 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) := by
  classical
  first
  | (simp only [formula_1243, shared_expr_Classification032_89, formula_1241, shared_expr_Classification032_87, formula_1242, shared_expr_Classification032_88, formula_1217, shared_expr_Classification031_171, formula_1218, shared_expr_Classification031_172, formula_1219, shared_expr_Classification031_173, formula_1220, shared_expr_Classification031_174, formula_179, formula_169, formula_167, formula_168, formula_172, formula_170, formula_171, formula_174, formula_173, formula_176, formula_175, formula_178, formula_177, formula_166, formula_165, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_965 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4274 (c2_depth r2_depth : Int) : (r2_depth ≤ c2_depth) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4275 (c2_depth r2_depth : Int) : (r2_depth ≥ c2_depth) ↔ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4276 (c2_depth r2_depth : Int) : ((r2_depth ≤ c2_depth) ∧ (r2_depth ≥ c2_depth)) ↔ ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (and_congr (normalization_4274 c2_depth r2_depth) (normalization_4275 c2_depth r2_depth))

abbrev shared_expr_Classification033_36 (c2_depth r2_depth : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
theorem normalization_4277 (c2_depth r2_depth : Int) : ((r2_depth = c2_depth) ↔ ((r2_depth ≤ c2_depth) ∧ (r2_depth ≥ c2_depth))) ↔ (shared_expr_Classification033_36 c2_depth r2_depth) := (iff_congr (normalization_4013 c2_depth r2_depth) (normalization_4276 c2_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_1619 (c2_depth r2_depth : Int) : ((r2_depth = c2_depth) ↔ ((r2_depth ≤ c2_depth) ∧ (r2_depth ≥ c2_depth))) := by
  classical
  have ht := (normalized_965 ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4277 c2_depth r2_depth) hn

theorem normalized_966 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4278 (c2_depth r2_depth : Int) : ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4279 (c2_depth r2_depth : Int) : ((r2_depth ≤ c2_depth) ↔ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_4274 c2_depth r2_depth) (normalization_4278 c2_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_1620 (c2_depth r2_depth : Int) : ((r2_depth ≤ c2_depth) ↔ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_966 ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4279 c2_depth r2_depth) hn

theorem normalized_967 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4280 (c2_depth r2_depth : Int) : ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4281 (c2_depth r2_depth : Int) : ((r2_depth ≥ c2_depth) ↔ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (iff_congr (normalization_4275 c2_depth r2_depth) (normalization_4280 c2_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_1621 (c2_depth r2_depth : Int) : ((r2_depth ≥ c2_depth) ↔ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_967 ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4281 c2_depth r2_depth) hn

theorem normalized_968 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4282 (c2_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (and_congr (normalization_4278 c2_depth r2_depth) (normalization_4280 c2_depth r2_depth))

theorem normalization_4283 (c2_depth r2_depth : Int) : (((r2_depth ≤ c2_depth) ∧ (r2_depth ≥ c2_depth)) ↔ (((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification033_36 c2_depth r2_depth) := (iff_congr (normalization_4276 c2_depth r2_depth) (normalization_4282 c2_depth r2_depth))

-- Checked replay of monotonicity.
theorem replay_1622 (c2_depth r2_depth : Int) : (((r2_depth ≤ c2_depth) ∧ (r2_depth ≥ c2_depth)) ↔ (((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_968 ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4279 c2_depth r2_depth) (replay_1620 c2_depth r2_depth)
  have n1 : (((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4281 c2_depth r2_depth) (replay_1621 c2_depth r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4283 c2_depth r2_depth) hn

abbrev shared_expr_Classification033_37 (c2_depth r2_depth : Int) : Prop := ((((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))))
abbrev formula_1259 (c2_depth r2_depth : Int) : Prop := (shared_expr_Classification033_37 c2_depth r2_depth)

theorem normalized_969 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4284 (c2_depth r2_depth : Int) : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_4278 c2_depth r2_depth))

theorem normalization_4285 (c2_depth r2_depth : Int) : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (not_congr (normalization_4280 c2_depth r2_depth))

theorem normalization_4286 (c2_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := (or_congr (normalization_4284 c2_depth r2_depth) (normalization_4285 c2_depth r2_depth))

theorem normalization_4287 (c2_depth r2_depth : Int) : (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))) := (not_congr (normalization_4286 c2_depth r2_depth))

abbrev shared_expr_Classification033_38 (c2_depth r2_depth : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))))
theorem normalization_4288 (c2_depth r2_depth : Int) : (formula_1259 c2_depth r2_depth) ↔ (shared_expr_Classification033_38 c2_depth r2_depth) := (iff_congr (normalization_4282 c2_depth r2_depth) (normalization_4287 c2_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_1623 (c2_depth r2_depth : Int) : (formula_1259 c2_depth r2_depth) := by
  classical
  have ht := (normalized_969 ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4288 c2_depth r2_depth) hn

theorem normalized_970 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4289 (c2_depth r2_depth : Int) : (((r2_depth ≤ c2_depth) ∧ (r2_depth ≥ c2_depth)) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification033_38 c2_depth r2_depth) := (iff_congr (normalization_4276 c2_depth r2_depth) (normalization_4287 c2_depth r2_depth))

-- Checked replay of trans.
theorem replay_1624 (c2_depth r2_depth : Int) : (((r2_depth ≤ c2_depth) ∧ (r2_depth ≥ c2_depth)) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_970 ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (shared_expr_Classification033_38 c2_depth r2_depth))
  have n0 : (shared_expr_Classification033_36 c2_depth r2_depth) := by
    exact Iff.mp (normalization_4283 c2_depth r2_depth) (replay_1622 c2_depth r2_depth)
  have n1 : (shared_expr_Classification033_38 c2_depth r2_depth) := by
    exact Iff.mp (normalization_4288 c2_depth r2_depth) (replay_1623 c2_depth r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4289 c2_depth r2_depth) hn

theorem normalized_971 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4290 (c2_depth r2_depth : Int) : ((r2_depth = c2_depth) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification033_38 c2_depth r2_depth) := (iff_congr (normalization_4013 c2_depth r2_depth) (normalization_4287 c2_depth r2_depth))

-- Checked replay of trans.
theorem replay_1625 (c2_depth r2_depth : Int) : ((r2_depth = c2_depth) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_971 ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (shared_expr_Classification033_38 c2_depth r2_depth))
  have n0 : (shared_expr_Classification033_36 c2_depth r2_depth) := by
    exact Iff.mp (normalization_4277 c2_depth r2_depth) (replay_1619 c2_depth r2_depth)
  have n1 : (shared_expr_Classification033_38 c2_depth r2_depth) := by
    exact Iff.mp (normalization_4289 c2_depth r2_depth) (replay_1624 c2_depth r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4290 c2_depth r2_depth) hn

theorem normalized_972 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4291 (r2_sign : Int) : ((r2_sign ≤ (0 : Int)) ∧ (r2_sign ≥ (0 : Int))) ↔ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) := (and_congr (normalization_306 r2_sign) (normalization_308 r2_sign))

theorem normalization_4292 (r2_sign : Int) : ((r2_sign = (0 : Int)) ↔ ((r2_sign ≤ (0 : Int)) ∧ (r2_sign ≥ (0 : Int)))) ↔ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ↔ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) := (iff_congr (normalization_153 r2_sign) (normalization_4291 r2_sign))

-- Checked replay of rewrite.
theorem replay_1626 (r2_sign : Int) : ((r2_sign = (0 : Int)) ↔ ((r2_sign ≤ (0 : Int)) ∧ (r2_sign ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_972 (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4292 r2_sign) hn

theorem normalized_973 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4293 (r2_sign : Int) : (((r2_sign ≤ (0 : Int)) ∧ (r2_sign ≥ (0 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))))) ↔ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_4291 r2_sign) (normalization_311 r2_sign))

-- Checked replay of rewrite.
theorem replay_1627 (r2_sign : Int) : (((r2_sign ≤ (0 : Int)) ∧ (r2_sign ≥ (0 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_973 ((r2_sign) ≤ (0 : Int)) ((r2_sign) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4293 r2_sign) hn

theorem normalized_974 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4294 (r2_sign : Int) : ((r2_sign = (0 : Int)) ↔ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))))) ↔ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_153 r2_sign) (normalization_311 r2_sign))

-- Checked replay of trans.
theorem replay_1628 (r2_sign : Int) : ((r2_sign = (0 : Int)) ↔ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_974 (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))))))
  have n0 : ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ↔ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_4292 r2_sign) (replay_1626 r2_sign)
  have n1 : ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_4293 r2_sign) (replay_1627 r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4294 r2_sign) hn

abbrev shared_expr_Classification033_39 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((r2_sign = (0 : Int)) ∧ (c2_sign = (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev formula_1260 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_39 c2_node c2_sign r2_node r2_sign)

theorem normalized_975 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4295 (c2_node c2_sign r2_node r2_sign : Int) : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_311 r2_sign) (and_congr (normalization_976 c2_sign) (normalization_4123 c2_node r2_node)))

abbrev shared_expr_Classification033_40 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ↔ ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))
theorem normalization_4296 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1260 c2_node c2_sign r2_node r2_sign) ↔ (shared_expr_Classification033_40 c2_node c2_sign r2_node r2_sign) := (iff_congr (normalization_4124 c2_node c2_sign r2_node r2_sign) (normalization_4295 c2_node c2_sign r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_1629 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1260 c2_node c2_sign r2_node r2_sign) := by
  classical
  have ht := (normalized_975 (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))) (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))) ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have n0 : ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_4294 r2_sign) (replay_1628 r2_sign)
  have n1 : ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1114 c2_sign) (replay_519 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4296 c2_node c2_sign r2_node r2_sign) hn

abbrev shared_expr_Classification033_41 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
abbrev formula_1261 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_41 c2_node c2_sign r2_node r2_sign)

theorem normalized_976 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4297 (c2_node r2_node : Int) : (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4123 c2_node r2_node))

theorem normalization_4298 (c2_node c2_sign r2_node r2_sign : Int) : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ↔ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) := (or_congr (normalization_307 r2_sign) (or_congr (normalization_309 r2_sign) (or_congr (normalization_972 c2_sign) (or_congr (normalization_974 c2_sign) (normalization_4297 c2_node r2_node)))))

theorem normalization_4299 (c2_node c2_sign r2_node r2_sign : Int) : (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_4298 c2_node c2_sign r2_node r2_sign))

abbrev shared_expr_Classification033_42 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))))
theorem normalization_4300 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1261 c2_node c2_sign r2_node r2_sign) ↔ (shared_expr_Classification033_42 c2_node c2_sign r2_node r2_sign) := (iff_congr (normalization_4295 c2_node c2_sign r2_node r2_sign) (normalization_4299 c2_node c2_sign r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1630 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1261 c2_node c2_sign r2_node r2_sign) := by
  classical
  have ht := (normalized_976 ((r2_sign) ≤ (0 : Int)) ((r2_sign) ≤ (-1 : Int)) ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4300 c2_node c2_sign r2_node r2_sign) hn

abbrev shared_expr_Classification033_43 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((r2_sign = (0 : Int)) ∧ (c2_sign = (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
abbrev formula_1262 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_43 c2_node c2_sign r2_node r2_sign)

theorem normalized_977 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_44 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))))
theorem normalization_4301 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1262 c2_node c2_sign r2_node r2_sign) ↔ (shared_expr_Classification033_44 c2_node c2_sign r2_node r2_sign) := (iff_congr (normalization_4124 c2_node c2_sign r2_node r2_sign) (normalization_4299 c2_node c2_sign r2_node r2_sign))

-- Checked replay of trans.
theorem replay_1631 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1262 c2_node c2_sign r2_node r2_sign) := by
  classical
  have ht := (normalized_977 ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))))
  have n0 : (shared_expr_Classification033_40 c2_node c2_sign r2_node r2_sign) := by
    exact Iff.mp (normalization_4296 c2_node c2_sign r2_node r2_sign) (replay_1629 c2_node c2_sign r2_node r2_sign)
  have n1 : (shared_expr_Classification033_42 c2_node c2_sign r2_node r2_sign) := by
    exact Iff.mp (normalization_4300 c2_node c2_sign r2_node r2_sign) (replay_1630 c2_node c2_sign r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4301 c2_node c2_sign r2_node r2_sign) hn

theorem normalized_978 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4302 (r2_sign : Int) : ((r2_sign ≤ (2 : Int)) ∧ (r2_sign ≥ (2 : Int))) ↔ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) := (and_congr (normalization_443 r2_sign) (normalization_445 r2_sign))

theorem normalization_4303 (r2_sign : Int) : ((r2_sign = (2 : Int)) ↔ ((r2_sign ≤ (2 : Int)) ∧ (r2_sign ≥ (2 : Int)))) ↔ ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ↔ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) := (iff_congr (normalization_362 r2_sign) (normalization_4302 r2_sign))

-- Checked replay of rewrite.
theorem replay_1632 (r2_sign : Int) : ((r2_sign = (2 : Int)) ↔ ((r2_sign ≤ (2 : Int)) ∧ (r2_sign ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_978 (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4303 r2_sign) hn

theorem normalized_979 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4304 (r2_sign : Int) : (((r2_sign ≤ (2 : Int)) ∧ (r2_sign ≥ (2 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ↔ ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_4302 r2_sign) (normalization_448 r2_sign))

-- Checked replay of rewrite.
theorem replay_1633 (r2_sign : Int) : (((r2_sign ≤ (2 : Int)) ∧ (r2_sign ≥ (2 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_979 ((r2_sign) ≤ (2 : Int)) ((r2_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4304 r2_sign) hn

theorem normalized_980 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4305 (r2_sign : Int) : ((r2_sign = (2 : Int)) ↔ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ↔ ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_362 r2_sign) (normalization_448 r2_sign))

-- Checked replay of trans.
theorem replay_1634 (r2_sign : Int) : ((r2_sign = (2 : Int)) ↔ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_980 (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int))))))))
  have n0 : ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ↔ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_4303 r2_sign) (replay_1632 r2_sign)
  have n1 : ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_4304 r2_sign) (replay_1633 r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4305 r2_sign) hn

theorem normalized_981 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4306 (h r2_depth : Int) : (r2_depth ≥ h) ↔ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4307 (h r2_depth : Int) : ((r2_depth ≤ h) ∧ (r2_depth ≥ h)) ↔ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (and_congr (normalization_358 h r2_depth) (normalization_4306 h r2_depth))

theorem normalization_4308 (h r2_depth : Int) : ((r2_depth = h) ↔ ((r2_depth ≤ h) ∧ (r2_depth ≥ h))) ↔ (((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := (iff_congr (normalization_361 h r2_depth) (normalization_4307 h r2_depth))

-- Checked replay of rewrite.
theorem replay_1635 (h r2_depth : Int) : ((r2_depth = h) ↔ ((r2_depth ≤ h) ∧ (r2_depth ≥ h))) := by
  classical
  have ht := (normalized_981 ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4308 h r2_depth) hn

theorem normalized_982 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4309 (h r2_depth : Int) : ((r2_depth ≤ h) ↔ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_358 h r2_depth) (normalization_383 h r2_depth))

-- Checked replay of rewrite.
theorem replay_1636 (h r2_depth : Int) : ((r2_depth ≤ h) ↔ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_982 ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4309 h r2_depth) hn

theorem normalized_983 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4310 (h r2_depth : Int) : ((r2_depth ≥ h) ↔ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ (((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ↔ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (iff_congr (normalization_4306 h r2_depth) (normalization_433 h r2_depth))

-- Checked replay of rewrite.
theorem replay_1637 (h r2_depth : Int) : ((r2_depth ≥ h) ↔ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_983 ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4310 h r2_depth) hn

theorem normalized_984 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4311 (h r2_depth : Int) : (((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (and_congr (normalization_383 h r2_depth) (normalization_433 h r2_depth))

theorem normalization_4312 (h r2_depth : Int) : (((r2_depth ≤ h) ∧ (r2_depth ≥ h)) ↔ (((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) ↔ (((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := (iff_congr (normalization_4307 h r2_depth) (normalization_4311 h r2_depth))

-- Checked replay of monotonicity.
theorem replay_1638 (h r2_depth : Int) : (((r2_depth ≤ h) ∧ (r2_depth ≥ h)) ↔ (((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := by
  classical
  have ht := (normalized_984 ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4309 h r2_depth) (replay_1636 h r2_depth)
  have n1 : (((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ↔ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4310 h r2_depth) (replay_1637 h r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4312 h r2_depth) hn

theorem normalized_985 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ p1) ∨ (¬ (¬ p0))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4313 (h r2_depth : Int) : (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_435 h r2_depth))

abbrev shared_expr_Classification033_45 (h r2_depth : Int) : Prop := (((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))))))
theorem normalization_4314 (h r2_depth : Int) : ((((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification033_45 h r2_depth) := (iff_congr (normalization_4311 h r2_depth) (normalization_4313 h r2_depth))

-- Checked replay of rewrite.
theorem replay_1639 (h r2_depth : Int) : ((((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_985 ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4314 h r2_depth) hn

theorem normalized_986 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4315 (h r2_depth : Int) : (((r2_depth ≤ h) ∧ (r2_depth ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification033_45 h r2_depth) := (iff_congr (normalization_4307 h r2_depth) (normalization_4313 h r2_depth))

-- Checked replay of trans.
theorem replay_1640 (h r2_depth : Int) : (((r2_depth ≤ h) ∧ (r2_depth ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_986 ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (shared_expr_Classification033_45 h r2_depth))
  have n0 : (((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := by
    exact Iff.mp (normalization_4312 h r2_depth) (replay_1638 h r2_depth)
  have n1 : (shared_expr_Classification033_45 h r2_depth) := by
    exact Iff.mp (normalization_4314 h r2_depth) (replay_1639 h r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4315 h r2_depth) hn

theorem normalized_987 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4316 (h r2_depth : Int) : ((r2_depth = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification033_45 h r2_depth) := (iff_congr (normalization_361 h r2_depth) (normalization_4313 h r2_depth))

-- Checked replay of trans.
theorem replay_1641 (h r2_depth : Int) : ((r2_depth = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_987 ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (shared_expr_Classification033_45 h r2_depth))
  have n0 : (((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := by
    exact Iff.mp (normalization_4308 h r2_depth) (replay_1635 h r2_depth)
  have n1 : (shared_expr_Classification033_45 h r2_depth) := by
    exact Iff.mp (normalization_4315 h r2_depth) (replay_1640 h r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4316 h r2_depth) hn

abbrev shared_expr_Classification033_46 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
abbrev formula_1263 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_46 c2_node c2_sign h r2_depth r2_node r2_sign)

theorem normalized_988 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∧ p2 ∧ p4 ∧ (¬ p6)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p5) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_47 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
theorem normalization_4317 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1263 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_47 c2_node c2_sign h r2_depth r2_node r2_sign) := (and_congr (normalization_448 r2_sign) (and_congr (normalization_982 c2_sign) (and_congr (normalization_4313 h r2_depth) (normalization_4123 c2_node r2_node))))

abbrev shared_expr_Classification033_48 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ∧ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
theorem normalization_4318 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (((r2_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r2_depth = h) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (formula_1263 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ ((shared_expr_Classification033_48 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_47 c2_node c2_sign h r2_depth r2_node r2_sign)) := (iff_congr (normalization_4125 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4317 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_1642 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (((r2_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r2_depth = h) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (formula_1263 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
  classical
  have ht := (normalized_988 (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int))))) (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int)))) ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))) ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have n0 : ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_4305 r2_sign) (replay_1634 r2_sign)
  have n1 : ((((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1135 c2_sign) (replay_528 c2_sign)
  have n2 : (shared_expr_Classification033_45 h r2_depth) := by
    exact Iff.mp (normalization_4316 h r2_depth) (replay_1641 h r2_depth)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4318 c2_node c2_sign h r2_depth r2_node r2_sign) hn

theorem normalized_989 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ ((¬ p4) ∨ (¬ (¬ p5)))) ∧ (¬ p6)) ↔ (¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p6))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_49 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int)))) ∨ (¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))
theorem normalization_4319 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign) := (or_congr (normalization_434 h r2_depth) (or_congr (normalization_428 h r2_depth) (or_congr (normalization_444 r2_sign) (or_congr (normalization_446 r2_sign) (or_congr (normalization_978 c2_sign) (or_congr (normalization_980 c2_sign) (normalization_4297 c2_node r2_node)))))))

theorem normalization_4320 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (¬ (formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (¬ (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign)) := (not_congr (normalization_4319 c2_node c2_sign h r2_depth r2_node r2_sign))

theorem normalization_4321 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1263 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign))) ↔ ((shared_expr_Classification033_47 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign))) := (iff_congr (normalization_4317 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4320 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1643 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1263 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
  classical
  have ht := (normalized_989 ((r2_sign) ≤ (2 : Int)) ((r2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (2 : Int)) ((c2_sign) ≤ (1 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4321 c2_node c2_sign h r2_depth r2_node r2_sign) hn

theorem normalized_990 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4322 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (((r2_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r2_depth = h) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ (formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign))) ↔ ((shared_expr_Classification033_48 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign))) := (iff_congr (normalization_4125 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4320 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of trans.
theorem replay_1644 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (((r2_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r2_depth = h) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ (formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
  classical
  have ht := (normalized_990 (shared_expr_Classification033_48 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_47 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign))
  have n0 : ((shared_expr_Classification033_48 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_47 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
    exact Iff.mp (normalization_4318 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1642 c2_node c2_sign h r2_depth r2_node r2_sign)
  have n1 : ((shared_expr_Classification033_47 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
    exact Iff.mp (normalization_4321 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1643 c2_node c2_sign h r2_depth r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4322 c2_node c2_sign h r2_depth r2_node r2_sign) hn

theorem normalized_991 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4323 (r2_sign : Int) : ((r2_sign ≤ (1 : Int)) ∧ (r2_sign ≥ (1 : Int))) ↔ (((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) := (and_congr (normalization_436 r2_sign) (normalization_438 r2_sign))

theorem normalization_4324 (r2_sign : Int) : ((r2_sign = (1 : Int)) ↔ ((r2_sign ≤ (1 : Int)) ∧ (r2_sign ≥ (1 : Int)))) ↔ ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ↔ (((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int))))) := (iff_congr (normalization_363 r2_sign) (normalization_4323 r2_sign))

-- Checked replay of rewrite.
theorem replay_1645 (r2_sign : Int) : ((r2_sign = (1 : Int)) ↔ ((r2_sign ≤ (1 : Int)) ∧ (r2_sign ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_991 (((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4324 r2_sign) hn

theorem normalized_992 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4325 (r2_sign : Int) : (((r2_sign ≤ (1 : Int)) ∧ (r2_sign ≥ (1 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))) ↔ ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_4323 r2_sign) (normalization_441 r2_sign))

-- Checked replay of rewrite.
theorem replay_1646 (r2_sign : Int) : (((r2_sign ≤ (1 : Int)) ∧ (r2_sign ≥ (1 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_992 ((r2_sign) ≤ (1 : Int)) ((r2_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4325 r2_sign) hn

theorem normalized_993 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4326 (r2_sign : Int) : ((r2_sign = (1 : Int)) ↔ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))) ↔ ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_363 r2_sign) (normalization_441 r2_sign))

-- Checked replay of trans.
theorem replay_1647 (r2_sign : Int) : ((r2_sign = (1 : Int)) ↔ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_993 (((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int))))))))
  have n0 : ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ↔ (((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_4324 r2_sign) (replay_1645 r2_sign)
  have n1 : ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_4325 r2_sign) (replay_1646 r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4326 r2_sign) hn

abbrev shared_expr_Classification033_50 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∧ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))
abbrev formula_1264 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_50 c2_node c2_sign h r2_depth r2_node r2_sign)

abbrev shared_expr_Classification033_51 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((r2_sign = (1 : Int)) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (formula_1264 c2_node c2_sign h r2_depth r2_node r2_sign))
abbrev formula_1265 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_51 c2_node c2_sign h r2_depth r2_node r2_sign)

theorem normalized_994 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4) ∧ (¬ p5)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4) ∧ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_52 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∧ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
theorem normalization_4327 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1264 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_52 c2_node c2_sign h r2_depth r2_node r2_sign) := (and_congr (normalization_441 r2_sign) (and_congr (normalization_1006 c2_sign) (and_congr (normalization_434 h r2_depth) (normalization_4127 c2_node r2_node))))

abbrev shared_expr_Classification033_53 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
theorem normalization_4328 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1265 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ ((shared_expr_Classification033_53 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_52 c2_node c2_sign h r2_depth r2_node r2_sign)) := (iff_congr (normalization_4128 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4327 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_1648 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1265 c2_node c2_sign h r2_depth r2_node r2_sign) := by
  classical
  have ht := (normalized_994 (((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int))))) (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)))
  have n0 : ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_4326 r2_sign) (replay_1647 r2_sign)
  have n1 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1170 c2_sign) (replay_544 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4328 c2_node c2_sign h r2_depth r2_node r2_sign) hn

theorem normalized_995 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4) ∧ (¬ p5)) ↔ (¬ (p4 ∨ p5 ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_54 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∨ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∨ (¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))
theorem normalization_4329 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1162 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign) := (or_congr (normalization_433 h r2_depth) (or_congr (normalization_4126 c2_node r2_node) (or_congr (normalization_437 r2_sign) (or_congr (normalization_439 r2_sign) (or_congr (normalization_1002 c2_sign) (normalization_1004 c2_sign))))))

theorem normalization_4330 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (¬ (formula_1162 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (¬ (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign)) := (not_congr (normalization_4329 c2_node c2_sign h r2_depth r2_node r2_sign))

theorem normalization_4331 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1264 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (formula_1162 c2_node c2_sign h r2_depth r2_node r2_sign))) ↔ ((shared_expr_Classification033_52 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign))) := (iff_congr (normalization_4327 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4330 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1649 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1264 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (formula_1162 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
  classical
  have ht := (normalized_995 ((r2_sign) ≤ (1 : Int)) ((r2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4331 c2_node c2_sign h r2_depth r2_node r2_sign) hn

abbrev shared_expr_Classification033_55 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((r2_sign = (1 : Int)) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (¬ (formula_1162 c2_node c2_sign h r2_depth r2_node r2_sign)))
abbrev formula_1266 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_55 c2_node c2_sign h r2_depth r2_node r2_sign)

theorem normalized_996 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4332 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1266 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ ((shared_expr_Classification033_53 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign))) := (iff_congr (normalization_4128 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4330 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of trans.
theorem replay_1650 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1266 c2_node c2_sign h r2_depth r2_node r2_sign) := by
  classical
  have ht := (normalized_996 (shared_expr_Classification033_53 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_52 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign))
  have n0 : ((shared_expr_Classification033_53 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_52 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
    exact Iff.mp (normalization_4328 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1648 c2_node c2_sign h r2_depth r2_node r2_sign)
  have n1 : ((shared_expr_Classification033_52 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
    exact Iff.mp (normalization_4331 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1649 c2_node c2_sign h r2_depth r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4332 c2_node c2_sign h r2_depth r2_node r2_sign) hn

abbrev shared_expr_Classification033_56 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ∨ (¬ (formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (¬ (formula_1162 c2_node c2_sign h r2_depth r2_node r2_sign)))
abbrev formula_1267 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_56 c2_node c2_sign h r2_depth r2_node r2_sign)

theorem normalized_997 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∨ p2 ∨ p4) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_57 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign)))
theorem normalization_4333 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1267 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_57 c2_node c2_sign h r2_depth r2_node r2_sign) := (or_congr (normalization_4299 c2_node c2_sign r2_node r2_sign) (or_congr (normalization_4320 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4330 c2_node c2_sign h r2_depth r2_node r2_sign)))

abbrev shared_expr_Classification033_58 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification033_48 c2_node c2_sign h r2_depth r2_node r2_sign) ∨ (shared_expr_Classification033_53 c2_node c2_sign h r2_depth r2_node r2_sign))
theorem normalization_4334 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (formula_1267 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ ((shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_57 c2_node c2_sign h r2_depth r2_node r2_sign)) := (iff_congr (normalization_4129 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4333 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_1651 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (formula_1267 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
  classical
  have ht := (normalized_997 ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) (shared_expr_Classification033_48 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_53 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign))
  have n0 : (shared_expr_Classification033_44 c2_node c2_sign r2_node r2_sign) := by
    exact Iff.mp (normalization_4301 c2_node c2_sign r2_node r2_sign) (replay_1631 c2_node c2_sign r2_node r2_sign)
  have n1 : ((shared_expr_Classification033_48 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
    exact Iff.mp (normalization_4322 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1644 c2_node c2_sign h r2_depth r2_node r2_sign)
  have n2 : ((shared_expr_Classification033_53 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
    exact Iff.mp (normalization_4332 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1650 c2_node c2_sign h r2_depth r2_node r2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4334 c2_node c2_sign h r2_depth r2_node r2_sign) hn

theorem normalized_998 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ↔ ((¬ p1) ∨ (¬ p0) ∨ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_59 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign)))
theorem normalization_4335 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign) := (or_congr (normalization_4320 c2_node c2_sign h r2_depth r2_node r2_sign) (or_congr (normalization_4299 c2_node c2_sign r2_node r2_sign) (normalization_4330 c2_node c2_sign h r2_depth r2_node r2_sign)))

theorem normalization_4336 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1267 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ ((shared_expr_Classification033_57 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign)) := (iff_congr (normalization_4333 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4335 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1652 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1267 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
  classical
  have ht := (normalized_998 ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) (shared_expr_Classification033_49 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_54 c2_node c2_sign h r2_depth r2_node r2_sign))
  have hn := ht
  exact Iff.mpr (normalization_4336 c2_node c2_sign h r2_depth r2_node r2_sign) hn

theorem normalized_999 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4337 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ ((shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign)) := (iff_congr (normalization_4129 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4335 c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of trans.
theorem replay_1653 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
  classical
  have ht := (normalized_999 (shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_57 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign))
  have n0 : ((shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_57 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
    exact Iff.mp (normalization_4334 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1651 c2_node c2_sign h r2_depth r2_node r2_sign)
  have n1 : ((shared_expr_Classification033_57 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
    exact Iff.mp (normalization_4336 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1652 c2_node c2_sign h r2_depth r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4337 c2_node c2_sign h r2_depth r2_node r2_sign) hn

abbrev shared_expr_Classification033_60 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((r2_depth = c2_depth) ∧ (formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ ((¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)))
abbrev formula_1268 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_60 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)

theorem normalized_1000 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_61 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))) ∧ (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign))
theorem normalization_4338 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (shared_expr_Classification033_61 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := (and_congr (normalization_4287 c2_depth r2_depth) (normalization_4335 c2_node c2_sign h r2_depth r2_node r2_sign))

abbrev shared_expr_Classification033_62 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (shared_expr_Classification033_61 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))
theorem normalization_4339 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1268 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_62 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := (iff_congr (normalization_4130 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4338 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_1654 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1268 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := by
  classical
  have ht := (normalized_1000 ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign))
  have n0 : (shared_expr_Classification033_38 c2_depth r2_depth) := by
    exact Iff.mp (normalization_4290 c2_depth r2_depth) (replay_1625 c2_depth r2_depth)
  have n1 : ((shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
    exact Iff.mp (normalization_4337 c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1653 c2_node c2_sign h r2_depth r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4339 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) hn

abbrev shared_expr_Classification033_63 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)))))
abbrev formula_1269 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_63 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)

theorem normalized_1001 (p0 p1 p2 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ p2) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4340 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (¬ (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign)) := (not_congr (normalization_4335 c2_node c2_sign h r2_depth r2_node r2_sign))

abbrev shared_expr_Classification033_64 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign)))
theorem normalization_4341 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign))) ↔ (shared_expr_Classification033_64 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := (or_congr (normalization_4284 c2_depth r2_depth) (or_congr (normalization_4285 c2_depth r2_depth) (normalization_4340 c2_node c2_sign h r2_depth r2_node r2_sign)))

theorem normalization_4342 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)))) ↔ (¬ (shared_expr_Classification033_64 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)) := (not_congr (normalization_4341 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))

theorem normalization_4343 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1269 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) ↔ ((shared_expr_Classification033_61 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_64 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))) := (iff_congr (normalization_4338 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4342 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1655 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1269 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := by
  classical
  have ht := (normalized_1001 ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) (shared_expr_Classification033_59 c2_node c2_sign h r2_depth r2_node r2_sign))
  have hn := ht
  exact Iff.mpr (normalization_4343 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) hn

abbrev shared_expr_Classification033_65 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((r2_depth = c2_depth) ∧ (formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)))))
abbrev formula_1270 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_65 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)

theorem normalized_1002 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_66 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (¬ (shared_expr_Classification033_64 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)))
theorem normalization_4344 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1270 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_66 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := (iff_congr (normalization_4130 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4342 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))

-- Checked replay of trans.
theorem replay_1656 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1270 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := by
  classical
  have ht := (normalized_1002 (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign)) (shared_expr_Classification033_61 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_64 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))
  have n0 : (shared_expr_Classification033_62 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := by
    exact Iff.mp (normalization_4339 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1654 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)
  have n1 : ((shared_expr_Classification033_61 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_64 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))) := by
    exact Iff.mp (normalization_4343 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1655 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4344 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) hn

theorem normalized_1003 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4345 (c2_depth r2_depth : Int) : ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_4346 (c2_depth r2_depth : Int) : ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ↔ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_4347 (c2_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := (and_congr (normalization_4345 c2_depth r2_depth) (normalization_4346 c2_depth r2_depth))

abbrev shared_expr_Classification033_67 (c2_depth r2_depth : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))
theorem normalization_4348 (c2_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification033_67 c2_depth r2_depth) := (iff_congr (normalization_4131 c2_depth r2_depth) (normalization_4347 c2_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_1657 (c2_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1003 ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4348 c2_depth r2_depth) hn

abbrev shared_expr_Classification033_68 (c2_depth r2_depth : Int) : Prop := ((((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))
abbrev formula_1271 (c2_depth r2_depth : Int) : Prop := (shared_expr_Classification033_68 c2_depth r2_depth)

theorem normalized_1004 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4349 (c2_depth r2_depth : Int) : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_4345 c2_depth r2_depth))

theorem normalization_4350 (c2_depth r2_depth : Int) : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := (not_congr (normalization_4346 c2_depth r2_depth))

theorem normalization_4351 (c2_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := (or_congr (normalization_4349 c2_depth r2_depth) (normalization_4350 c2_depth r2_depth))

theorem normalization_4352 (c2_depth r2_depth : Int) : (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) := (not_congr (normalization_4351 c2_depth r2_depth))

abbrev shared_expr_Classification033_69 (c2_depth r2_depth : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))))
theorem normalization_4353 (c2_depth r2_depth : Int) : (formula_1271 c2_depth r2_depth) ↔ (shared_expr_Classification033_69 c2_depth r2_depth) := (iff_congr (normalization_4347 c2_depth r2_depth) (normalization_4352 c2_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_1658 (c2_depth r2_depth : Int) : (formula_1271 c2_depth r2_depth) := by
  classical
  have ht := (normalized_1004 ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)) ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4353 c2_depth r2_depth) hn

theorem normalized_1005 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4354 (c2_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification033_69 c2_depth r2_depth) := (iff_congr (normalization_4131 c2_depth r2_depth) (normalization_4352 c2_depth r2_depth))

-- Checked replay of trans.
theorem replay_1659 (c2_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1005 ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) (shared_expr_Classification033_69 c2_depth r2_depth))
  have n0 : (shared_expr_Classification033_67 c2_depth r2_depth) := by
    exact Iff.mp (normalization_4348 c2_depth r2_depth) (replay_1657 c2_depth r2_depth)
  have n1 : (shared_expr_Classification033_69 c2_depth r2_depth) := by
    exact Iff.mp (normalization_4353 c2_depth r2_depth) (replay_1658 c2_depth r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4354 c2_depth r2_depth) hn

theorem normalized_1006 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ∧ (p4 ∧ (¬ p5)) ∧ p6) ∨ (((p3 ∧ (¬ p0)) ∨ (p2 ∧ (¬ p3))) ∧ (p7 ∧ (¬ p4)) ∧ (¬ (¬ p8)))) ↔ ((¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) ∨ (¬ p6))) ∨ (¬ ((¬ p8) ∨ (¬ p7) ∨ (¬ (¬ p4)) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ (¬ p0)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4355 (r2_sign : Int) : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int))))))) := (or_congr (normalization_311 r2_sign) (normalization_448 r2_sign))

theorem normalization_4356 (r2_sign : Int) : (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_4355 r2_sign))

theorem normalization_4357 (c2_node r2_node : Int) : (¬ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_4132 c2_node r2_node))

abbrev shared_expr_Classification033_70 (c2_node c2_sign r2_node r2_sign : Int) : Prop := ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int)))))))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_4358 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1164 c2_node c2_sign r2_node r2_sign) ↔ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign) := (or_congr (normalization_972 c2_sign) (or_congr (normalization_974 c2_sign) (or_congr (normalization_4356 r2_sign) (normalization_4357 c2_node r2_node))))

theorem normalization_4359 (c2_node c2_sign r2_node r2_sign : Int) : (¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ↔ (¬ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign)) := (not_congr (normalization_4358 c2_node c2_sign r2_node r2_sign))

theorem normalization_4360 (r2_sign : Int) : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int))))))) := (or_congr (normalization_441 r2_sign) (normalization_448 r2_sign))

theorem normalization_4361 (r2_sign : Int) : (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_4360 r2_sign))

abbrev shared_expr_Classification033_71 (c2_node c2_sign r2_node r2_sign : Int) : Prop := ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (1 : Int)))))))))
theorem normalization_4362 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1165 c2_node c2_sign r2_node r2_sign) ↔ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign) := (or_congr (normalization_4134 c2_node r2_node) (or_congr (normalization_1002 c2_sign) (or_congr (normalization_1004 c2_sign) (normalization_4361 r2_sign))))

theorem normalization_4363 (c2_node c2_sign r2_node r2_sign : Int) : (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)) ↔ (¬ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign)) := (not_congr (normalization_4362 c2_node c2_sign r2_node r2_sign))

theorem normalization_4364 (c2_node c2_sign r2_node r2_sign : Int) : ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign))) ↔ ((¬ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign))) := (or_congr (normalization_4359 c2_node c2_sign r2_node r2_sign) (normalization_4363 c2_node c2_sign r2_node r2_sign))

abbrev shared_expr_Classification033_72 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
abbrev shared_expr_Classification033_73 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification033_74 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((shared_expr_Classification033_72 c2_node c2_sign r2_node r2_sign) ∨ (shared_expr_Classification033_73 c2_node c2_sign r2_node r2_sign)) ↔ ((¬ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign))))
theorem normalization_4365 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1245 c2_node c2_sign r2_node r2_sign) ↔ ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)))) ↔ (shared_expr_Classification033_74 c2_node c2_sign r2_node r2_sign) := (iff_congr (normalization_4137 c2_node c2_sign r2_node r2_sign) (normalization_4364 c2_node c2_sign r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1660 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1245 c2_node c2_sign r2_node r2_sign) ↔ ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)))) := by
  classical
  have ht := (normalized_1006 ((r2_sign) ≤ (0 : Int)) ((r2_sign) ≤ (-1 : Int)) ((r2_sign) ≤ (2 : Int)) ((r2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c2_sign) ≤ (1 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4365 c2_node c2_sign r2_node r2_sign) hn

abbrev shared_expr_Classification033_75 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ∧ ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign))))
abbrev formula_1272 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification033_75 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)

theorem normalized_1007 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_76 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ∧ ((¬ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign))))
theorem normalization_4366 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : (formula_1272 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_76 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) := (and_congr (normalization_4352 c2_depth r2_depth) (normalization_4364 c2_node c2_sign r2_node r2_sign))

abbrev shared_expr_Classification033_77 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification033_72 c2_node c2_sign r2_node r2_sign) ∨ (shared_expr_Classification033_73 c2_node c2_sign r2_node r2_sign)))
theorem normalization_4367 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : ((((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1245 c2_node c2_sign r2_node r2_sign)) ↔ (formula_1272 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)) ↔ ((shared_expr_Classification033_77 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_76 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)) := (iff_congr (normalization_4138 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (normalization_4366 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_1661 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : ((((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1245 c2_node c2_sign r2_node r2_sign)) ↔ (formula_1272 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)) := by
  classical
  have ht := (normalized_1007 ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ((shared_expr_Classification033_72 c2_node c2_sign r2_node r2_sign) ∨ (shared_expr_Classification033_73 c2_node c2_sign r2_node r2_sign)) ((¬ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign))))
  have n0 : (shared_expr_Classification033_69 c2_depth r2_depth) := by
    exact Iff.mp (normalization_4354 c2_depth r2_depth) (replay_1659 c2_depth r2_depth)
  have n1 : (shared_expr_Classification033_74 c2_node c2_sign r2_node r2_sign) := by
    exact Iff.mp (normalization_4365 c2_node c2_sign r2_node r2_sign) (replay_1660 c2_node c2_sign r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4367 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) hn

theorem normalized_1008 (p0 p1 p2 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ p2) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4368 (c2_node c2_sign r2_node r2_sign : Int) : (¬ ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)))) ↔ (¬ ((¬ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign)))) := (not_congr (normalization_4364 c2_node c2_sign r2_node r2_sign))

abbrev shared_expr_Classification033_78 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : Prop := ((¬ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ ((¬ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign)))))
theorem normalization_4369 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) := (or_congr (normalization_4349 c2_depth r2_depth) (or_congr (normalization_4350 c2_depth r2_depth) (normalization_4368 c2_node c2_sign r2_node r2_sign)))

theorem normalization_4370 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)) ↔ (¬ (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)) := (not_congr (normalization_4369 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))

theorem normalization_4371 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : ((formula_1272 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) ↔ ((shared_expr_Classification033_76 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) := (iff_congr (normalization_4366 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (normalization_4370 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1662 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : ((formula_1272 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) := by
  classical
  have ht := (normalized_1008 ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)) ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((¬ (shared_expr_Classification033_70 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_71 c2_node c2_sign r2_node r2_sign))))
  have hn := ht
  exact Iff.mpr (normalization_4371 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) hn

theorem normalized_1009 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4372 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : ((((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1245 c2_node c2_sign r2_node r2_sign)) ↔ (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) ↔ ((shared_expr_Classification033_77 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) := (iff_congr (normalization_4138 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (normalization_4370 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))

-- Checked replay of trans.
theorem replay_1663 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : ((((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1245 c2_node c2_sign r2_node r2_sign)) ↔ (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) := by
  classical
  have ht := (normalized_1009 (shared_expr_Classification033_77 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (shared_expr_Classification033_76 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))
  have n0 : ((shared_expr_Classification033_77 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Classification033_76 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)) := by
    exact Iff.mp (normalization_4367 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (replay_1661 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)
  have n1 : ((shared_expr_Classification033_76 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) := by
    exact Iff.mp (normalization_4371 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (replay_1662 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4372 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) hn

theorem normalized_1010 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5)) ∧ (p6 ↔ (¬ p7))) → ((p0 ∨ p2 ∨ p4 ∨ p6) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5) ∨ (¬ p7)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification033_79 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification033_64 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (¬ (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)))
theorem normalization_4373 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Classification033_79 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := (or_congr (normalization_288 r2_kind) (or_congr (normalization_992 c2_kind) (or_congr (normalization_4342 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4370 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))))

abbrev shared_expr_Classification033_80 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∨ (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (shared_expr_Classification033_77 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))
abbrev shared_expr_Classification033_81 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((shared_expr_Classification033_80 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Classification033_79 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign))
theorem normalization_4374 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : ((formula_1246 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) ↔ (shared_expr_Classification033_81 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := (iff_congr (normalization_4139 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (normalization_4373 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_1664 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : ((formula_1246 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) := by
  classical
  have ht := (normalized_1010 (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int))))) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))) (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification033_58 c2_node c2_sign h r2_depth r2_node r2_sign)) (shared_expr_Classification033_64 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (shared_expr_Classification033_77 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))
  have n0 : ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_589 r2_kind) (replay_149 r2_kind)
  have n1 : ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1083 c2_kind) (replay_506 c2_kind)
  have n2 : (shared_expr_Classification033_66 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := by
    exact Iff.mp (normalization_4344 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (replay_1656 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)
  have n3 : ((shared_expr_Classification033_77 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ↔ (¬ (shared_expr_Classification033_78 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) := by
    exact Iff.mp (normalization_4372 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (replay_1663 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_4374 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) hn

end H4Formal.Generated.Classification
