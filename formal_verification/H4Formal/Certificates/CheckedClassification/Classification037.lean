import H4Formal.BooleanReplaySupport
import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification036

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Classification037_0 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ (formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_1357 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_0 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_1062 (p0 : Prop) : ((p0 ↔ True) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification037_1 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := (((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
abbrev shared_expr_Classification037_2 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_3 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_2 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification037_4 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_5 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_4 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification037_6 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_7 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_2 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_6 c1_depth c1_kind c1_node c1_sign r3_level)))
abbrev shared_expr_Classification037_8 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_9 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_2 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_8 c1_depth c1_kind c1_node c1_sign r3_level)))
abbrev shared_expr_Classification037_10 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_11 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_10 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_4 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification037_12 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_13 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_12 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_4 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification037_14 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_3 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_5 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification037_7 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification037_9 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification037_11 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification037_13 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))
abbrev shared_expr_Classification037_15 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_14 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Classification037_16 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_17 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_18 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_16 c1_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_17 c1_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Classification037_19 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_20 (c1_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_21 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_19 c1_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_20 c1_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Classification037_22 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_23 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_22 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_24 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_25 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_24 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_26 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_27 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_26 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_28 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_29 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_28 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_30 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_mode) ≤ (0 : Int)) ∧ (¬ ((c1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_18 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((((c1_mode) ≤ (1 : Int)) ∧ (¬ ((c1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_21 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((((c1_mode) ≤ (2 : Int)) ∧ (¬ ((c1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification037_23 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (3 : Int)) ∧ (¬ ((c1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification037_25 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (4 : Int)) ∧ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification037_27 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (5 : Int)) ∧ (¬ ((c1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification037_29 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Classification037_31 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
abbrev shared_expr_Classification037_32 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification037_33 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification037_31 c1_node c1_sign r3_node r3_sign) ∨ (shared_expr_Classification037_32 c1_node c1_sign r3_node r3_sign)))
abbrev shared_expr_Classification037_34 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ∧ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_35 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_36 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((shared_expr_Classification037_34 c1_node c1_sign h r3_depth r3_node r3_sign) ∨ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification037_35 c1_node c1_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Classification037_37 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ∨ (shared_expr_Classification037_33 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ∨ (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification037_36 c1_node c1_sign h r3_depth r3_node r3_sign)))
abbrev shared_expr_Classification037_38 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_30 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_37 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Classification037_39 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_15 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_38 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Classification037_40 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ (shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_4573 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1357 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification037_40 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_4571 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_4568 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1867 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1357 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_1062 (shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_4573 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

abbrev shared_expr_Classification037_41 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((formula_1334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ (formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_1358 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_41 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_1063 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification037_42 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_43 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((shared_expr_Classification037_42 c1_depth c1_kind c1_sign r3_level) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_44 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_2 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_43 c1_depth c1_kind c1_node c1_sign r3_level)))
abbrev shared_expr_Classification037_45 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((shared_expr_Classification037_42 c1_depth c1_kind c1_sign r3_level) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_46 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_2 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_45 c1_depth c1_kind c1_node c1_sign r3_level)))
abbrev shared_expr_Classification037_47 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_48 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((shared_expr_Classification037_47 c1_depth c1_kind c1_sign r3_level) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_49 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_48 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_4 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification037_50 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((shared_expr_Classification037_47 c1_depth c1_kind c1_sign r3_level) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_51 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_50 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_4 c1_depth c1_kind c1_sign r3_level)))
abbrev shared_expr_Classification037_52 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_3 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_5 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification037_44 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification037_46 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification037_49 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification037_51 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))
abbrev shared_expr_Classification037_53 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_52 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Classification037_54 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification037_16 c1_level r3_depth r3_kind r3_sign) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_55 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_54 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_56 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification037_16 c1_level r3_depth r3_kind r3_sign) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_57 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_56 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_58 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification037_20 c1_level r3_depth r3_kind r3_sign) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification037_59 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_58 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_60 (c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification037_20 c1_level r3_depth r3_kind r3_sign) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification037_61 (c1_group c1_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_60 c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification037_62 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_mode) ≤ (0 : Int)) ∧ (¬ ((c1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_18 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((((c1_mode) ≤ (1 : Int)) ∧ (¬ ((c1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_21 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((((c1_mode) ≤ (2 : Int)) ∧ (¬ ((c1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification037_55 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (3 : Int)) ∧ (¬ ((c1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification037_57 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (4 : Int)) ∧ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification037_59 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c1_mode) ≤ (5 : Int)) ∧ (¬ ((c1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification037_61 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Classification037_63 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification037_35 c1_node c1_sign h r3_depth r3_node r3_sign) ∨ (shared_expr_Classification037_34 c1_node c1_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Classification037_64 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
abbrev shared_expr_Classification037_65 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification037_31 c1_node c1_sign r3_node r3_sign) ∨ (shared_expr_Classification037_64 c1_node c1_sign r3_node r3_sign)))
abbrev shared_expr_Classification037_66 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification037_63 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (shared_expr_Classification037_65 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))
abbrev shared_expr_Classification037_67 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Classification037_66 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Classification037_68 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ True) ∨ (shared_expr_Classification037_67 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
abbrev shared_expr_Classification037_69 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_62 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_68 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Classification037_70 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_53 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_69 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Classification037_71 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((shared_expr_Classification037_70 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ (shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_4574 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1358 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification037_71 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_4570 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_4568 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of trans.
abbrev shared_expr_Classification037_72 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((shared_expr_Classification037_70 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ ((shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True))
theorem replay_1868 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1358 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_1063 ((shared_expr_Classification037_70 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ((shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) (shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have n0 : (shared_expr_Classification037_72 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
    exact Iff.mp (normalization_4572 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_1866 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have n1 : (shared_expr_Classification037_40 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
    exact Iff.mp (normalization_4573 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_1867 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4574 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_1869 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i147 : ((formula_1334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_1868 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) i147

abbrev shared_expr_Classification037_73 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((formula_1353 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_1353 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
abbrev formula_1359 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_73 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

theorem normalized_1064 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification037_74 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Classification037_38 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification037_38 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_4575 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification037_74 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (iff_congr (normalization_4567 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (normalization_4567 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1870 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
  classical
  have ht := (normalized_1064 (shared_expr_Classification037_38 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_4575 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) hn

abbrev shared_expr_Classification037_75 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_1360 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_75 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_1065 (p0 p1 : Prop) : (((p0 ↔ p0)) → (p1 ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification037_76 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_4576 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1360 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification037_76 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_4568 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_4568 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_1871 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1360 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_1065 (shared_expr_Classification037_38 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have n0 : (shared_expr_Classification037_74 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := by
    exact Iff.mp (normalization_4575 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) (replay_1870 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_4576 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_1872 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i147 : ((formula_1334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_1871 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_1869 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i147)

theorem normalized_1066 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of rewrite.
theorem replay_1873 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1360 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_1066 (shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_4576 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_1874 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i147 : ((formula_1334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_1873 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_1872 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i147)

-- Checked replay of mp.
theorem replay_1875 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i147 : ((formula_1334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_1871 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_1874 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i147)

-- Checked replay of mp.
theorem replay_1876 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i147 : ((formula_1334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_1871 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_1875 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i147)

abbrev shared_expr_Classification037_77 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ (c1_kind = (2 : Int))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c1_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int))))))
abbrev formula_1361 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (shared_expr_Classification037_77 c1_depth c1_kind c1_sign r3_group r3_level)

abbrev shared_expr_Classification037_78 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ (c1_kind = (2 : Int))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c1_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))))))
abbrev formula_1362 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (shared_expr_Classification037_78 c1_depth c1_kind c1_sign r3_group r3_level)

abbrev shared_expr_Classification037_79 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c1_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int))))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c1_kind = (1 : Int)) ∧ (c1_depth = r3_level) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int))) ∧ ((c1_node % (2 : Int)) = (0 : Int)))))
abbrev formula_1363 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (shared_expr_Classification037_79 c1_depth c1_kind c1_node c1_sign r3_group r3_level)

abbrev shared_expr_Classification037_80 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c1_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int))))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c1_kind = (1 : Int)) ∧ (c1_depth = r3_level) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int))) ∧ ((c1_node % (2 : Int)) = (1 : Int)))))
abbrev formula_1364 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (shared_expr_Classification037_80 c1_depth c1_kind c1_node c1_sign r3_group r3_level)

abbrev shared_expr_Classification037_81 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c1_kind = (1 : Int)) ∧ (c1_depth = r3_level) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))) ∧ ((c1_node % (2 : Int)) = (0 : Int)))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c1_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))))))
abbrev formula_1365 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (shared_expr_Classification037_81 c1_depth c1_kind c1_node c1_sign r3_group r3_level)

abbrev shared_expr_Classification037_82 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c1_kind = (1 : Int)) ∧ (c1_depth = r3_level) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))) ∧ ((c1_node % (2 : Int)) = (1 : Int)))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c1_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))))))
abbrev formula_1366 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (shared_expr_Classification037_82 c1_depth c1_kind c1_node c1_sign r3_group r3_level)

abbrev shared_expr_Classification037_83 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((r3_mode = (0 : Int)) ∧ (formula_1361 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((r3_mode = (1 : Int)) ∧ (formula_1362 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((r3_mode = (2 : Int)) ∧ (formula_1363 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((r3_mode = (3 : Int)) ∧ (formula_1364 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((r3_mode = (4 : Int)) ∧ (formula_1365 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((r3_mode = (5 : Int)) ∧ (formula_1366 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))
abbrev formula_1367 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification037_83 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)

abbrev shared_expr_Classification037_84 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((c1_kind = (0 : Int)) ∧ ((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group)))) ∨ ((¬ (c1_kind = (0 : Int))) ∧ (formula_1367 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
abbrev formula_1368 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification037_84 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

abbrev shared_expr_Classification037_85 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (((c1_group = (1 : Int)) ∧ ((r3_kind = (1 : Int)) ∧ (r3_depth = c1_level) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))))) ∨ ((¬ (c1_group = (1 : Int))) ∧ ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_level)) = (-1 : Int)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))))))
abbrev formula_1369 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Classification037_85 c1_group c1_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Classification037_86 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (((c1_group = (1 : Int)) ∧ ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_level)) = (-1 : Int)) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))))) ∨ ((¬ (c1_group = (1 : Int))) ∧ ((r3_kind = (1 : Int)) ∧ (r3_depth = c1_level) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))))))
abbrev formula_1370 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Classification037_86 c1_group c1_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Classification037_87 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((c1_mode = (0 : Int)) ∧ (formula_1369 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((c1_mode = (1 : Int)) ∧ (formula_1370 c1_group c1_level r3_depth r3_kind r3_sign)) ∨ ((c1_mode = (2 : Int)) ∧ (formula_1345 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c1_mode = (3 : Int)) ∧ (formula_1346 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c1_mode = (4 : Int)) ∧ (formula_1347 c1_group c1_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c1_mode = (5 : Int)) ∧ (formula_1348 c1_group c1_level r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1371 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_87 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Classification037_88 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_sign = (0 : Int)) ∧ (c1_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ ((r3_sign = (2 : Int)) ∧ (c1_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ ((r3_sign = (1 : Int)) ∧ (c1_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))
abbrev formula_1372 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_88 c1_node c1_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Classification037_89 (c1_node c1_sign r3_node r3_sign : Int) : Prop := ((((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c1_sign = (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ∨ (((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c1_sign = (1 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_1373 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_89 c1_node c1_sign r3_node r3_sign)

abbrev shared_expr_Classification037_90 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((r3_kind = (2 : Int)) ∨ (c1_kind = (2 : Int)) ∨ ((r3_depth = c1_depth) ∧ (formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ (formula_1373 c1_node c1_sign r3_node r3_sign)))
abbrev formula_1374 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_90 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Classification037_91 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((c1_kind = (0 : Int)) ∧ (formula_1371 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (c1_kind = (0 : Int))) ∧ (formula_1374 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1375 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_91 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Classification037_92 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((r3_kind = (0 : Int)) ∧ (formula_1368 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) ∨ ((¬ (r3_kind = (0 : Int))) ∧ (formula_1375 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1376 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_92 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Classification037_93 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((formula_1354 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_1376 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_1377 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Classification037_93 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

set_option maxHeartbeats 2000000 in
theorem normalized_1067 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)) ∨ (((¬ p52) ∧ p53) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p54) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p55))))) ∨ (((¬ p53) ∧ p56) ∧ (((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p59)) ∨ ((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p59)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p60))))))))) ↔ (((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)) ∨ (((¬ p53) ∧ p56) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p59)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p59)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p60)))) ∨ (((¬ p52) ∧ p53) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p54) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p55))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4577 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ ((¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

abbrev shared_expr_Classification037_94 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
theorem normalization_4578 (c1_depth c1_kind c1_sign r3_level : Int) : ((c1_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (shared_expr_Classification037_94 c1_depth c1_kind c1_sign r3_level) := (and_congr (normalization_1323 c1_kind) (and_congr (normalization_4577 c1_depth r3_level) (normalization_1327 c1_sign)))

abbrev shared_expr_Classification037_95 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_94 c1_depth c1_kind c1_sign r3_level)))
theorem normalization_4579 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (formula_1361 c1_depth c1_kind c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_95 c1_depth c1_kind c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2291 r3_group) (normalization_1322 c1_kind)) (and_congr (not_congr (normalization_2291 r3_group)) (normalization_4578 c1_depth c1_kind c1_sign r3_level)))

theorem normalization_4580 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (0 : Int)) ∧ (formula_1361 c1_depth c1_kind c1_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_95 c1_depth c1_kind c1_sign r3_group r3_level)) := (and_congr (normalization_2290 r3_mode) (normalization_4579 c1_depth c1_kind c1_sign r3_group r3_level))

abbrev shared_expr_Classification037_96 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
theorem normalization_4581 (c1_depth c1_kind c1_sign r3_level : Int) : ((c1_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (shared_expr_Classification037_96 c1_depth c1_kind c1_sign r3_level) := (and_congr (normalization_1323 c1_kind) (and_congr (normalization_4577 c1_depth r3_level) (normalization_1332 c1_sign)))

abbrev shared_expr_Classification037_97 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_96 c1_depth c1_kind c1_sign r3_level)))
theorem normalization_4582 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (formula_1362 c1_depth c1_kind c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_97 c1_depth c1_kind c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2291 r3_group) (normalization_1322 c1_kind)) (and_congr (not_congr (normalization_2291 r3_group)) (normalization_4581 c1_depth c1_kind c1_sign r3_level)))

theorem normalization_4583 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (1 : Int)) ∧ (formula_1362 c1_depth c1_kind c1_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_97 c1_depth c1_kind c1_sign r3_group r3_level)) := (and_congr (normalization_2296 r3_mode) (normalization_4582 c1_depth c1_kind c1_sign r3_group r3_level))

abbrev shared_expr_Classification037_98 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_94 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_6 c1_depth c1_kind c1_node c1_sign r3_level)))
theorem normalization_4584 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1363 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_98 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2291 r3_group) (normalization_4578 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2291 r3_group)) (normalization_4521 c1_depth c1_kind c1_node c1_sign r3_level)))

theorem normalization_4585 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (2 : Int)) ∧ (formula_1363 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification037_98 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (and_congr (normalization_2300 r3_mode) (normalization_4584 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

abbrev shared_expr_Classification037_99 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_94 c1_depth c1_kind c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_8 c1_depth c1_kind c1_node c1_sign r3_level)))
theorem normalization_4586 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1364 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_99 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2291 r3_group) (normalization_4578 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2291 r3_group)) (normalization_4524 c1_depth c1_kind c1_node c1_sign r3_level)))

theorem normalization_4587 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (3 : Int)) ∧ (formula_1364 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification037_99 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (and_congr (normalization_2306 r3_mode) (normalization_4586 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

abbrev shared_expr_Classification037_100 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_10 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_96 c1_depth c1_kind c1_sign r3_level)))
theorem normalization_4588 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1365 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_100 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2291 r3_group) (normalization_4527 c1_depth c1_kind c1_node c1_sign r3_level)) (and_congr (not_congr (normalization_2291 r3_group)) (normalization_4581 c1_depth c1_kind c1_sign r3_level)))

theorem normalization_4589 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (4 : Int)) ∧ (formula_1365 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification037_100 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (and_congr (normalization_2310 r3_mode) (normalization_4588 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

abbrev shared_expr_Classification037_101 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_12 c1_depth c1_kind c1_node c1_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification037_96 c1_depth c1_kind c1_sign r3_level)))
theorem normalization_4590 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1366 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_101 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2291 r3_group) (normalization_4530 c1_depth c1_kind c1_node c1_sign r3_level)) (and_congr (not_congr (normalization_2291 r3_group)) (normalization_4581 c1_depth c1_kind c1_sign r3_level)))

theorem normalization_4591 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (5 : Int)) ∧ (formula_1366 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification037_101 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (and_congr (normalization_2315 r3_mode) (normalization_4590 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

abbrev shared_expr_Classification037_102 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_95 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_97 c1_depth c1_kind c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification037_98 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification037_99 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification037_100 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification037_101 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))
theorem normalization_4592 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1367 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_102 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) := (or_congr (normalization_4580 c1_depth c1_kind c1_sign r3_group r3_level r3_mode) (or_congr (normalization_4583 c1_depth c1_kind c1_sign r3_group r3_level r3_mode) (or_congr (normalization_4585 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (or_congr (normalization_4587 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (or_congr (normalization_4589 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (normalization_4591 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))))))

abbrev shared_expr_Classification037_103 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_102 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
theorem normalization_4593 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1368 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_103 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_1317 c1_kind) (normalization_4513 c1_group c1_level c1_mode r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_1317 c1_kind)) (normalization_4592 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))

theorem normalization_4594 (c1_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_level)) = (-1 : Int)) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_4595 (c1_level r3_depth r3_kind r3_sign : Int) : ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_level)) = (-1 : Int)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int)))) ↔ (shared_expr_Classification037_17 c1_level r3_depth r3_kind r3_sign) := (and_congr (normalization_467 r3_kind) (and_congr (normalization_4594 c1_level r3_depth) (normalization_2323 r3_sign)))

theorem normalization_4596 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (formula_1369 c1_group c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Classification037_18 c1_group c1_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_1356 c1_group) (normalization_4469 c1_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_1356 c1_group)) (normalization_4595 c1_level r3_depth r3_kind r3_sign)))

theorem normalization_4597 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : ((c1_mode = (0 : Int)) ∧ (formula_1369 c1_group c1_level r3_depth r3_kind r3_sign)) ↔ ((((c1_mode) ≤ (0 : Int)) ∧ (¬ ((c1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_18 c1_group c1_level r3_depth r3_kind r3_sign)) := (and_congr (normalization_1355 c1_mode) (normalization_4596 c1_group c1_level r3_depth r3_kind r3_sign))

theorem normalization_4598 (c1_level r3_depth r3_kind r3_sign : Int) : ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c1_level)) = (-1 : Int)) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int)))) ↔ (shared_expr_Classification037_19 c1_level r3_depth r3_kind r3_sign) := (and_congr (normalization_467 r3_kind) (and_congr (normalization_4594 c1_level r3_depth) (normalization_2330 r3_sign)))

theorem normalization_4599 (c1_group c1_level r3_depth r3_kind r3_sign : Int) : (formula_1370 c1_group c1_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Classification037_21 c1_group c1_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_1356 c1_group) (normalization_4598 c1_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_1356 c1_group)) (normalization_4475 c1_level r3_depth r3_kind r3_sign)))

theorem normalization_4600 (c1_group c1_level c1_mode r3_depth r3_kind r3_sign : Int) : ((c1_mode = (1 : Int)) ∧ (formula_1370 c1_group c1_level r3_depth r3_kind r3_sign)) ↔ ((((c1_mode) ≤ (1 : Int)) ∧ (¬ ((c1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification037_21 c1_group c1_level r3_depth r3_kind r3_sign)) := (and_congr (normalization_1363 c1_mode) (normalization_4599 c1_group c1_level r3_depth r3_kind r3_sign))

theorem normalization_4601 (c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign : Int) : (formula_1371 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification037_30 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_4597 c1_group c1_level c1_mode r3_depth r3_kind r3_sign) (or_congr (normalization_4600 c1_group c1_level c1_mode r3_depth r3_kind r3_sign) (or_congr (normalization_4544 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_4547 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_4550 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign) (normalization_4553 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign))))))

theorem normalization_4602 (c1_node r3_node : Int) : ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ↔ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4603 (c1_node c1_sign r3_node r3_sign : Int) : ((r3_sign = (0 : Int)) ∧ (c1_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_472 r3_sign) (and_congr (normalization_1325 c1_sign) (normalization_4602 c1_node r3_node)))

theorem normalization_4604 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((r3_sign = (2 : Int)) ∧ (c1_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (shared_expr_Classification037_34 c1_node c1_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2322 r3_sign) (and_congr (normalization_1326 c1_sign) (and_congr (normalization_2357 h r3_depth) (normalization_4602 c1_node r3_node))))

theorem normalization_4605 (c1_node r3_node : Int) : ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) ↔ ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4606 (c1_node r3_node : Int) : (¬ ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) := (not_congr (normalization_4605 c1_node r3_node))

theorem normalization_4607 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((r3_sign = (1 : Int)) ∧ (c1_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification037_35 c1_node c1_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2329 r3_sign) (and_congr (normalization_1331 c1_sign) (and_congr (normalization_2469 h r3_depth) (normalization_4606 c1_node r3_node))))

abbrev shared_expr_Classification037_104 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification037_34 c1_node c1_sign h r3_depth r3_node r3_sign) ∨ (shared_expr_Classification037_35 c1_node c1_sign h r3_depth r3_node r3_sign))
theorem normalization_4608 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Classification037_104 c1_node c1_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_4603 c1_node c1_sign r3_node r3_sign) (or_congr (normalization_4604 c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4607 c1_node c1_sign h r3_depth r3_node r3_sign)))

theorem normalization_4609 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((r3_depth = c1_depth) ∧ (formula_1372 c1_node c1_sign h r3_depth r3_node r3_sign)) ↔ (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification037_104 c1_node c1_sign h r3_depth r3_node r3_sign)) := (and_congr (normalization_4492 c1_depth r3_depth) (normalization_4608 c1_node c1_sign h r3_depth r3_node r3_sign))

theorem normalization_4610 (c1_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ ((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4611 (c1_node r3_node : Int) : ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4612 (c1_node c1_sign r3_node r3_sign : Int) : (((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c1_sign = (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (shared_expr_Classification037_31 c1_node c1_sign r3_node r3_sign) := (and_congr (normalization_2323 r3_sign) (and_congr (normalization_1325 c1_sign) (normalization_4611 c1_node r3_node)))

theorem normalization_4613 (c1_node r3_node : Int) : ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4614 (c1_node r3_node : Int) : (¬ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4613 c1_node r3_node))

theorem normalization_4615 (c1_node c1_sign r3_node r3_sign : Int) : (((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c1_sign = (1 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))) ↔ (shared_expr_Classification037_32 c1_node c1_sign r3_node r3_sign) := (and_congr (normalization_2330 r3_sign) (and_congr (normalization_1331 c1_sign) (normalization_4614 c1_node r3_node)))

theorem normalization_4616 (c1_node c1_sign r3_node r3_sign : Int) : (formula_1373 c1_node c1_sign r3_node r3_sign) ↔ ((shared_expr_Classification037_31 c1_node c1_sign r3_node r3_sign) ∨ (shared_expr_Classification037_32 c1_node c1_sign r3_node r3_sign)) := (or_congr (normalization_4612 c1_node c1_sign r3_node r3_sign) (normalization_4615 c1_node c1_sign r3_node r3_sign))

theorem normalization_4617 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : (((r3_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ (formula_1373 c1_node c1_sign r3_node r3_sign)) ↔ (shared_expr_Classification037_33 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) := (and_congr (normalization_4610 c1_depth r3_depth) (normalization_4616 c1_node c1_sign r3_node r3_sign))

abbrev shared_expr_Classification037_105 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ∨ (((¬ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification037_104 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (shared_expr_Classification037_33 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))
theorem normalization_4618 (c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1374 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification037_105 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_469 r3_kind) (or_congr (normalization_1322 c1_kind) (or_congr (normalization_4609 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (normalization_4617 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))))

abbrev shared_expr_Classification037_106 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_30 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_105 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
theorem normalization_4619 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1375 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Classification037_106 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_1317 c1_kind) (normalization_4601 c1_group c1_level c1_mode r3_depth r3_kind r3_node r3_sign)) (and_congr (not_congr (normalization_1317 c1_kind)) (normalization_4618 c1_depth c1_kind c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Classification037_107 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification037_103 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification037_106 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))
theorem normalization_4620 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1376 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification037_107 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (and_congr (normalization_455 r3_kind) (normalization_4593 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_455 r3_kind)) (normalization_4619 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Classification037_108 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Classification037_39 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification037_107 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_4621 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1377 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Classification037_108 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_4568 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_4620 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_1877 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1377 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_1067 ((r3_kind) ≤ (0 : Int)) ((r3_kind) ≤ (-1 : Int)) ((c1_kind) ≤ (0 : Int)) ((c1_kind) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ((r3_mode) ≤ (0 : Int)) ((r3_mode) ≤ (-1 : Int)) ((r3_group) ≤ (1 : Int)) ((r3_group) ≤ (0 : Int)) ((c1_kind) ≤ (2 : Int)) ((c1_kind) ≤ (1 : Int)) ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)) ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)) ((c1_sign) ≤ (2 : Int)) ((c1_sign) ≤ (1 : Int)) ((r3_mode) ≤ (1 : Int)) ((r3_mode) ≤ (2 : Int)) ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((r3_mode) ≤ (3 : Int)) ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int)) ((r3_mode) ≤ (4 : Int)) ((r3_mode) ≤ (5 : Int)) ((c1_mode) ≤ (0 : Int)) ((c1_mode) ≤ (-1 : Int)) ((c1_group) ≤ (1 : Int)) ((c1_group) ≤ (0 : Int)) ((r3_kind) ≤ (1 : Int)) ((c1_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)) ((c1_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int)) ((c1_mode) ≤ (1 : Int)) ((c1_mode) ≤ (2 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ((r3_kind) ≤ (2 : Int)) ((c1_mode) ≤ (3 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int)) ((c1_mode) ≤ (4 : Int)) ((c1_mode) ≤ (5 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)) ((c1_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4621 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_1878 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i147 : ((formula_1334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1376 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_1877 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_1876 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i147)

theorem normalized_1068 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4622 (c1_mode r3_mode : Int) : (r3_mode ≤ c1_mode) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4623 (c1_mode r3_mode : Int) : (r3_mode ≥ c1_mode) ↔ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_4624 (c1_mode r3_mode : Int) : ((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_4622 c1_mode r3_mode) (normalization_4623 c1_mode r3_mode))

abbrev shared_expr_Classification037_109 (c1_mode r3_mode : Int) : Prop := (((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
theorem normalization_4625 (c1_mode r3_mode : Int) : ((r3_mode = c1_mode) ↔ ((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode))) ↔ (shared_expr_Classification037_109 c1_mode r3_mode) := (iff_congr (normalization_4440 c1_mode r3_mode) (normalization_4624 c1_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_1879 (c1_mode r3_mode : Int) : ((r3_mode = c1_mode) ↔ ((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode))) := by
  classical
  have ht := (normalized_1068 ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4625 c1_mode r3_mode) hn

theorem normalized_1069 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4626 (c1_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4627 (c1_mode r3_mode : Int) : ((r3_mode ≤ c1_mode) ↔ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ↔ ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_4622 c1_mode r3_mode) (normalization_4626 c1_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_1880 (c1_mode r3_mode : Int) : ((r3_mode ≤ c1_mode) ↔ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1069 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4627 c1_mode r3_mode) hn

theorem normalized_1070 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4628 (c1_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) ↔ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_4629 (c1_mode r3_mode : Int) : ((r3_mode ≥ c1_mode) ↔ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ (((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (iff_congr (normalization_4623 c1_mode r3_mode) (normalization_4628 c1_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_1881 (c1_mode r3_mode : Int) : ((r3_mode ≥ c1_mode) ↔ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1070 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4629 c1_mode r3_mode) hn

theorem normalized_1071 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4630 (c1_mode r3_mode : Int) : (((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_4626 c1_mode r3_mode) (normalization_4628 c1_mode r3_mode))

theorem normalization_4631 (c1_mode r3_mode : Int) : (((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ (((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Classification037_109 c1_mode r3_mode) := (iff_congr (normalization_4624 c1_mode r3_mode) (normalization_4630 c1_mode r3_mode))

-- Checked replay of monotonicity.
theorem replay_1882 (c1_mode r3_mode : Int) : (((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ (((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1071 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4627 c1_mode r3_mode) (replay_1880 c1_mode r3_mode)
  have n1 : (((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4629 c1_mode r3_mode) (replay_1881 c1_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4631 c1_mode r3_mode) hn

abbrev shared_expr_Classification037_110 (c1_mode r3_mode : Int) : Prop := ((((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))))
abbrev formula_1378 (c1_mode r3_mode : Int) : Prop := (shared_expr_Classification037_110 c1_mode r3_mode)

theorem normalized_1072 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4632 (c1_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_4626 c1_mode r3_mode))

theorem normalization_4633 (c1_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (not_congr (normalization_4628 c1_mode r3_mode))

theorem normalization_4634 (c1_mode r3_mode : Int) : ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) := (or_congr (normalization_4632 c1_mode r3_mode) (normalization_4633 c1_mode r3_mode))

theorem normalization_4635 (c1_mode r3_mode : Int) : (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) := (not_congr (normalization_4634 c1_mode r3_mode))

abbrev shared_expr_Classification037_111 (c1_mode r3_mode : Int) : Prop := (((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))))
theorem normalization_4636 (c1_mode r3_mode : Int) : (formula_1378 c1_mode r3_mode) ↔ (shared_expr_Classification037_111 c1_mode r3_mode) := (iff_congr (normalization_4630 c1_mode r3_mode) (normalization_4635 c1_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_1883 (c1_mode r3_mode : Int) : (formula_1378 c1_mode r3_mode) := by
  classical
  have ht := (normalized_1072 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4636 c1_mode r3_mode) hn

theorem normalized_1073 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4637 (c1_mode r3_mode : Int) : (((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification037_111 c1_mode r3_mode) := (iff_congr (normalization_4624 c1_mode r3_mode) (normalization_4635 c1_mode r3_mode))

-- Checked replay of trans.
theorem replay_1884 (c1_mode r3_mode : Int) : (((r3_mode ≤ c1_mode) ∧ (r3_mode ≥ c1_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1073 ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Classification037_111 c1_mode r3_mode))
  have n0 : (shared_expr_Classification037_109 c1_mode r3_mode) := by
    exact Iff.mp (normalization_4631 c1_mode r3_mode) (replay_1882 c1_mode r3_mode)
  have n1 : (shared_expr_Classification037_111 c1_mode r3_mode) := by
    exact Iff.mp (normalization_4636 c1_mode r3_mode) (replay_1883 c1_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4637 c1_mode r3_mode) hn

theorem normalized_1074 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4638 (c1_mode r3_mode : Int) : ((r3_mode = c1_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification037_111 c1_mode r3_mode) := (iff_congr (normalization_4440 c1_mode r3_mode) (normalization_4635 c1_mode r3_mode))

-- Checked replay of trans.
theorem replay_1885 (c1_mode r3_mode : Int) : ((r3_mode = c1_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1074 ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Classification037_111 c1_mode r3_mode))
  have n0 : (shared_expr_Classification037_109 c1_mode r3_mode) := by
    exact Iff.mp (normalization_4625 c1_mode r3_mode) (replay_1879 c1_mode r3_mode)
  have n1 : (shared_expr_Classification037_111 c1_mode r3_mode) := by
    exact Iff.mp (normalization_4637 c1_mode r3_mode) (replay_1884 c1_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4638 c1_mode r3_mode) hn

theorem normalized_1075 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4639 (c1_level r3_level : Int) : (r3_level ≤ c1_level) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4640 (c1_level r3_level : Int) : (r3_level ≥ c1_level) ↔ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4641 (c1_level r3_level : Int) : ((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_4639 c1_level r3_level) (normalization_4640 c1_level r3_level))

abbrev shared_expr_Classification037_112 (c1_level r3_level : Int) : Prop := (((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
theorem normalization_4642 (c1_level r3_level : Int) : ((r3_level = c1_level) ↔ ((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level))) ↔ (shared_expr_Classification037_112 c1_level r3_level) := (iff_congr (normalization_4441 c1_level r3_level) (normalization_4641 c1_level r3_level))

-- Checked replay of rewrite.
theorem replay_1886 (c1_level r3_level : Int) : ((r3_level = c1_level) ↔ ((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level))) := by
  classical
  have ht := (normalized_1075 ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4642 c1_level r3_level) hn

theorem normalized_1076 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4643 (c1_level r3_level : Int) : ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4644 (c1_level r3_level : Int) : ((r3_level ≤ c1_level) ↔ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_4639 c1_level r3_level) (normalization_4643 c1_level r3_level))

-- Checked replay of rewrite.
theorem replay_1887 (c1_level r3_level : Int) : ((r3_level ≤ c1_level) ↔ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1076 ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4644 c1_level r3_level) hn

theorem normalized_1077 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4645 (c1_level r3_level : Int) : ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4646 (c1_level r3_level : Int) : ((r3_level ≥ c1_level) ↔ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (iff_congr (normalization_4640 c1_level r3_level) (normalization_4645 c1_level r3_level))

-- Checked replay of rewrite.
theorem replay_1888 (c1_level r3_level : Int) : ((r3_level ≥ c1_level) ↔ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1077 ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4646 c1_level r3_level) hn

theorem normalized_1078 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4647 (c1_level r3_level : Int) : (((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_4643 c1_level r3_level) (normalization_4645 c1_level r3_level))

theorem normalization_4648 (c1_level r3_level : Int) : (((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ (((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ↔ (shared_expr_Classification037_112 c1_level r3_level) := (iff_congr (normalization_4641 c1_level r3_level) (normalization_4647 c1_level r3_level))

-- Checked replay of monotonicity.
theorem replay_1889 (c1_level r3_level : Int) : (((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ (((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1078 ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4644 c1_level r3_level) (replay_1887 c1_level r3_level)
  have n1 : (((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4646 c1_level r3_level) (replay_1888 c1_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4648 c1_level r3_level) hn

abbrev shared_expr_Classification037_113 (c1_level r3_level : Int) : Prop := ((((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))))
abbrev formula_1379 (c1_level r3_level : Int) : Prop := (shared_expr_Classification037_113 c1_level r3_level)

theorem normalized_1079 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4649 (c1_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4643 c1_level r3_level))

theorem normalization_4650 (c1_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_4645 c1_level r3_level))

theorem normalization_4651 (c1_level r3_level : Int) : ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) := (or_congr (normalization_4649 c1_level r3_level) (normalization_4650 c1_level r3_level))

theorem normalization_4652 (c1_level r3_level : Int) : (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) := (not_congr (normalization_4651 c1_level r3_level))

abbrev shared_expr_Classification037_114 (c1_level r3_level : Int) : Prop := (((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))))
theorem normalization_4653 (c1_level r3_level : Int) : (formula_1379 c1_level r3_level) ↔ (shared_expr_Classification037_114 c1_level r3_level) := (iff_congr (normalization_4647 c1_level r3_level) (normalization_4652 c1_level r3_level))

-- Checked replay of rewrite.
theorem replay_1890 (c1_level r3_level : Int) : (formula_1379 c1_level r3_level) := by
  classical
  have ht := (normalized_1079 ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4653 c1_level r3_level) hn

theorem normalized_1080 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4654 (c1_level r3_level : Int) : (((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification037_114 c1_level r3_level) := (iff_congr (normalization_4641 c1_level r3_level) (normalization_4652 c1_level r3_level))

-- Checked replay of trans.
theorem replay_1891 (c1_level r3_level : Int) : (((r3_level ≤ c1_level) ∧ (r3_level ≥ c1_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1080 ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Classification037_114 c1_level r3_level))
  have n0 : (shared_expr_Classification037_112 c1_level r3_level) := by
    exact Iff.mp (normalization_4648 c1_level r3_level) (replay_1889 c1_level r3_level)
  have n1 : (shared_expr_Classification037_114 c1_level r3_level) := by
    exact Iff.mp (normalization_4653 c1_level r3_level) (replay_1890 c1_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4654 c1_level r3_level) hn

theorem normalized_1081 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4655 (c1_level r3_level : Int) : ((r3_level = c1_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification037_114 c1_level r3_level) := (iff_congr (normalization_4441 c1_level r3_level) (normalization_4652 c1_level r3_level))

-- Checked replay of trans.
theorem replay_1892 (c1_level r3_level : Int) : ((r3_level = c1_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1081 ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Classification037_114 c1_level r3_level))
  have n0 : (shared_expr_Classification037_112 c1_level r3_level) := by
    exact Iff.mp (normalization_4642 c1_level r3_level) (replay_1886 c1_level r3_level)
  have n1 : (shared_expr_Classification037_114 c1_level r3_level) := by
    exact Iff.mp (normalization_4654 c1_level r3_level) (replay_1891 c1_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4655 c1_level r3_level) hn

theorem normalized_1082 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4656 (c1_group r3_group : Int) : (r3_group ≤ c1_group) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4657 (c1_group r3_group : Int) : (r3_group ≥ c1_group) ↔ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_4658 (c1_group r3_group : Int) : ((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_4656 c1_group r3_group) (normalization_4657 c1_group r3_group))

abbrev shared_expr_Classification037_115 (c1_group r3_group : Int) : Prop := (((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
theorem normalization_4659 (c1_group r3_group : Int) : ((r3_group = c1_group) ↔ ((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group))) ↔ (shared_expr_Classification037_115 c1_group r3_group) := (iff_congr (normalization_4511 c1_group r3_group) (normalization_4658 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_1893 (c1_group r3_group : Int) : ((r3_group = c1_group) ↔ ((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group))) := by
  classical
  have ht := (normalized_1082 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4659 c1_group r3_group) hn

theorem normalized_1083 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4660 (c1_group r3_group : Int) : ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4661 (c1_group r3_group : Int) : ((r3_group ≤ c1_group) ↔ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ↔ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_4656 c1_group r3_group) (normalization_4660 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_1894 (c1_group r3_group : Int) : ((r3_group ≤ c1_group) ↔ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1083 ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4661 c1_group r3_group) hn

theorem normalized_1084 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4662 (c1_group r3_group : Int) : ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)) ↔ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_4663 (c1_group r3_group : Int) : ((r3_group ≥ c1_group) ↔ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ (((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (iff_congr (normalization_4657 c1_group r3_group) (normalization_4662 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_1895 (c1_group r3_group : Int) : ((r3_group ≥ c1_group) ↔ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1084 ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4663 c1_group r3_group) hn

theorem normalized_1085 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4664 (c1_group r3_group : Int) : (((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_4660 c1_group r3_group) (normalization_4662 c1_group r3_group))

theorem normalization_4665 (c1_group r3_group : Int) : (((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ (((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) ↔ (shared_expr_Classification037_115 c1_group r3_group) := (iff_congr (normalization_4658 c1_group r3_group) (normalization_4664 c1_group r3_group))

-- Checked replay of monotonicity.
theorem replay_1896 (c1_group r3_group : Int) : (((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ (((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1085 ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4661 c1_group r3_group) (replay_1894 c1_group r3_group)
  have n1 : (((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4663 c1_group r3_group) (replay_1895 c1_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4665 c1_group r3_group) hn

abbrev shared_expr_Classification037_116 (c1_group r3_group : Int) : Prop := ((((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))))
abbrev formula_1380 (c1_group r3_group : Int) : Prop := (shared_expr_Classification037_116 c1_group r3_group)

theorem normalized_1086 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4666 (c1_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_4660 c1_group r3_group))

theorem normalization_4667 (c1_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (not_congr (normalization_4662 c1_group r3_group))

theorem normalization_4668 (c1_group r3_group : Int) : ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) := (or_congr (normalization_4666 c1_group r3_group) (normalization_4667 c1_group r3_group))

theorem normalization_4669 (c1_group r3_group : Int) : (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))) := (not_congr (normalization_4668 c1_group r3_group))

abbrev shared_expr_Classification037_117 (c1_group r3_group : Int) : Prop := (((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_4670 (c1_group r3_group : Int) : (formula_1380 c1_group r3_group) ↔ (shared_expr_Classification037_117 c1_group r3_group) := (iff_congr (normalization_4664 c1_group r3_group) (normalization_4669 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_1897 (c1_group r3_group : Int) : (formula_1380 c1_group r3_group) := by
  classical
  have ht := (normalized_1086 ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4670 c1_group r3_group) hn

theorem normalized_1087 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4671 (c1_group r3_group : Int) : (((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification037_117 c1_group r3_group) := (iff_congr (normalization_4658 c1_group r3_group) (normalization_4669 c1_group r3_group))

-- Checked replay of trans.
theorem replay_1898 (c1_group r3_group : Int) : (((r3_group ≤ c1_group) ∧ (r3_group ≥ c1_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1087 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Classification037_117 c1_group r3_group))
  have n0 : (shared_expr_Classification037_115 c1_group r3_group) := by
    exact Iff.mp (normalization_4665 c1_group r3_group) (replay_1896 c1_group r3_group)
  have n1 : (shared_expr_Classification037_117 c1_group r3_group) := by
    exact Iff.mp (normalization_4670 c1_group r3_group) (replay_1897 c1_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4671 c1_group r3_group) hn

theorem normalized_1088 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4672 (c1_group r3_group : Int) : ((r3_group = c1_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification037_117 c1_group r3_group) := (iff_congr (normalization_4511 c1_group r3_group) (normalization_4669 c1_group r3_group))

-- Checked replay of trans.
theorem replay_1899 (c1_group r3_group : Int) : ((r3_group = c1_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1088 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Classification037_117 c1_group r3_group))
  have n0 : (shared_expr_Classification037_115 c1_group r3_group) := by
    exact Iff.mp (normalization_4659 c1_group r3_group) (replay_1893 c1_group r3_group)
  have n1 : (shared_expr_Classification037_117 c1_group r3_group) := by
    exact Iff.mp (normalization_4671 c1_group r3_group) (replay_1898 c1_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4672 c1_group r3_group) hn

theorem normalized_1089 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4673 (c1_group r3_group : Int) : (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) := (not_congr (normalization_4669 c1_group r3_group))

abbrev shared_expr_Classification037_118 (c1_group r3_group : Int) : Prop := ((¬ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))))
theorem normalization_4674 (c1_group r3_group : Int) : ((¬ (r3_group = c1_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Classification037_118 c1_group r3_group) := (iff_congr (normalization_4512 c1_group r3_group) (normalization_4673 c1_group r3_group))

-- Checked replay of monotonicity.
theorem replay_1900 (c1_group r3_group : Int) : ((¬ (r3_group = c1_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1089 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification037_117 c1_group r3_group) := by
    exact Iff.mp (normalization_4672 c1_group r3_group) (replay_1899 c1_group r3_group)
  have hn := ht n0
  exact Iff.mpr (normalization_4674 c1_group r3_group) hn

abbrev shared_expr_Classification037_119 (c1_group r3_group : Int) : Prop := ((¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))
abbrev formula_1381 (c1_group r3_group : Int) : Prop := (shared_expr_Classification037_119 c1_group r3_group)

theorem normalized_1090 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification037_120 (c1_group r3_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_4675 (c1_group r3_group : Int) : (formula_1381 c1_group r3_group) ↔ (shared_expr_Classification037_120 c1_group r3_group) := (iff_congr (normalization_4673 c1_group r3_group) (normalization_4668 c1_group r3_group))

-- Checked replay of rewrite.
theorem replay_1901 (c1_group r3_group : Int) : (formula_1381 c1_group r3_group) := by
  classical
  have ht := (normalized_1090 ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4675 c1_group r3_group) hn

theorem normalized_1091 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification037_121 (c1_group r3_group : Int) : Prop := ((¬ ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_4676 (c1_group r3_group : Int) : ((¬ (r3_group = c1_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))) ↔ (shared_expr_Classification037_121 c1_group r3_group) := (iff_congr (normalization_4512 c1_group r3_group) (normalization_4668 c1_group r3_group))

-- Checked replay of trans.
theorem replay_1902 (c1_group r3_group : Int) : ((¬ (r3_group = c1_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1091 ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification037_118 c1_group r3_group) := by
    exact Iff.mp (normalization_4674 c1_group r3_group) (replay_1900 c1_group r3_group)
  have n1 : (shared_expr_Classification037_120 c1_group r3_group) := by
    exact Iff.mp (normalization_4675 c1_group r3_group) (replay_1901 c1_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4676 c1_group r3_group) hn

abbrev shared_expr_Classification037_122 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r3_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))) ∧ ((¬ ((r3_group + ((-1 : Int) * c1_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))
abbrev formula_1382 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification037_122 c1_group c1_level c1_mode r3_group r3_level r3_mode)

theorem normalized_1092 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification037_123 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_4677 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (formula_1382 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_123 c1_group c1_level c1_mode r3_group r3_level r3_mode) := (and_congr (normalization_4635 c1_mode r3_mode) (and_congr (normalization_4652 c1_level r3_level) (normalization_4668 c1_group r3_group)))

theorem normalization_4678 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group))) ↔ (formula_1382 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ↔ ((shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_123 c1_group c1_level c1_mode r3_group r3_level r3_mode)) := (iff_congr (normalization_4513 c1_group c1_level c1_mode r3_group r3_level r3_mode) (normalization_4677 c1_group c1_level c1_mode r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_1903 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group))) ↔ (formula_1382 c1_group c1_level c1_mode r3_group r3_level r3_mode)) := by
  classical
  have ht := (normalized_1092 ((¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) ((¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ((¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) ((¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification037_111 c1_mode r3_mode) := by
    exact Iff.mp (normalization_4638 c1_mode r3_mode) (replay_1885 c1_mode r3_mode)
  have n1 : (shared_expr_Classification037_114 c1_level r3_level) := by
    exact Iff.mp (normalization_4655 c1_level r3_level) (replay_1892 c1_level r3_level)
  have n2 : (shared_expr_Classification037_121 c1_group r3_group) := by
    exact Iff.mp (normalization_4676 c1_group r3_group) (replay_1902 c1_group r3_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4678 c1_group c1_level c1_mode r3_group r3_level r3_mode) hn

theorem normalized_1093 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification037_124 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_4679 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (formula_1311 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode) := (or_congr (normalization_4632 c1_mode r3_mode) (or_congr (normalization_4633 c1_mode r3_mode) (or_congr (normalization_4649 c1_level r3_level) (or_congr (normalization_4650 c1_level r3_level) (normalization_4669 c1_group r3_group)))))

theorem normalization_4680 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (¬ (formula_1311 c1_group c1_level c1_mode r3_group r3_level r3_mode)) ↔ (¬ (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode)) := (not_congr (normalization_4679 c1_group c1_level c1_mode r3_group r3_level r3_mode))

theorem normalization_4681 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : ((formula_1382 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (formula_1311 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Classification037_123 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_4677 c1_group c1_level c1_mode r3_group r3_level r3_mode) (normalization_4680 c1_group c1_level c1_mode r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_1904 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : ((formula_1382 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (formula_1311 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_1093 ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4681 c1_group c1_level c1_mode r3_group r3_level r3_mode) hn

theorem normalized_1094 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4682 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group))) ↔ (¬ (formula_1311 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_4513 c1_group c1_level c1_mode r3_group r3_level r3_mode) (normalization_4680 c1_group c1_level c1_mode r3_group r3_level r3_mode))

-- Checked replay of trans.
theorem replay_1905 (c1_group c1_level c1_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c1_mode) ∧ (r3_level = c1_level) ∧ (¬ (r3_group = c1_group))) ↔ (¬ (formula_1311 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_1094 (shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Classification037_123 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode))
  have n0 : ((shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_123 c1_group c1_level c1_mode r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_4678 c1_group c1_level c1_mode r3_group r3_level r3_mode) (replay_1903 c1_group c1_level c1_mode r3_group r3_level r3_mode)
  have n1 : ((shared_expr_Classification037_123 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_4681 c1_group c1_level c1_mode r3_group r3_level r3_mode) (replay_1904 c1_group c1_level c1_mode r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4682 c1_group c1_level c1_mode r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_1906 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((formula_1367 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1310 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) := by
  classical
  first
  | (simp only [formula_1367, shared_expr_Classification037_83, formula_1361, shared_expr_Classification037_77, formula_1362, shared_expr_Classification037_78, formula_1363, shared_expr_Classification037_79, formula_1364, shared_expr_Classification037_80, formula_1365, shared_expr_Classification037_81, formula_1366, shared_expr_Classification037_82, formula_1310, shared_expr_Classification036_21, formula_1299, shared_expr_Classification036_10, formula_1298, shared_expr_Classification036_9, formula_1301, shared_expr_Classification036_12, formula_1300, shared_expr_Classification036_11, formula_1303, shared_expr_Classification036_14, formula_1302, shared_expr_Classification036_13, formula_1305, shared_expr_Classification036_16, formula_1304, shared_expr_Classification036_15, formula_1307, shared_expr_Classification036_18, formula_1306, shared_expr_Classification036_17, formula_1309, shared_expr_Classification036_20, formula_1308, shared_expr_Classification036_19, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Classification037_125 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∧ (¬ (formula_1311 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ∧ (formula_1310 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
abbrev formula_1383 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification037_125 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

abbrev shared_expr_Classification037_126 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_1368 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1383 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
abbrev formula_1384 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification037_126 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode)

theorem normalized_1095 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4683 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_4684 (c1_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) := (not_congr (normalization_4683 c1_depth r3_level))

theorem normalization_4685 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_4686 (c1_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := (not_congr (normalization_4685 c1_depth r3_level))

abbrev shared_expr_Classification037_127 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_4687 (c1_depth c1_kind c1_sign r3_level : Int) : (formula_1298 c1_depth c1_kind c1_sign r3_level) ↔ (shared_expr_Classification037_127 c1_depth c1_kind c1_sign r3_level) := (or_congr (normalization_1588 c1_kind) (or_congr (normalization_1590 c1_kind) (or_congr (normalization_1608 c1_sign) (or_congr (normalization_4684 c1_depth r3_level) (normalization_4686 c1_depth r3_level)))))

theorem normalization_4688 (c1_depth c1_kind c1_sign r3_level : Int) : (¬ (formula_1298 c1_depth c1_kind c1_sign r3_level)) ↔ (¬ (shared_expr_Classification037_127 c1_depth c1_kind c1_sign r3_level)) := (not_congr (normalization_4687 c1_depth c1_kind c1_sign r3_level))

abbrev shared_expr_Classification037_128 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification037_127 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
theorem normalization_4689 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (formula_1299 c1_depth c1_kind c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_128 c1_depth c1_kind c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_4688 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_1616 c1_kind)))

theorem normalization_4690 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (¬ (formula_1299 c1_depth c1_kind c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification037_128 c1_depth c1_kind c1_sign r3_group r3_level)) := (not_congr (normalization_4689 c1_depth c1_kind c1_sign r3_group r3_level))

theorem normalization_4691 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_1299 c1_depth c1_kind c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification037_128 c1_depth c1_kind c1_sign r3_group r3_level))) := (or_congr (normalization_2549 r3_mode) (or_congr (normalization_2551 r3_mode) (normalization_4690 c1_depth c1_kind c1_sign r3_group r3_level)))

theorem normalization_4692 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_1299 c1_depth c1_kind c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification037_128 c1_depth c1_kind c1_sign r3_group r3_level)))) := (not_congr (normalization_4691 c1_depth c1_kind c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification037_129 (c1_depth c1_kind c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_4693 (c1_depth c1_kind c1_sign r3_level : Int) : (formula_1300 c1_depth c1_kind c1_sign r3_level) ↔ (shared_expr_Classification037_129 c1_depth c1_kind c1_sign r3_level) := (or_congr (normalization_1588 c1_kind) (or_congr (normalization_1590 c1_kind) (or_congr (normalization_1628 c1_sign) (or_congr (normalization_4684 c1_depth r3_level) (normalization_4686 c1_depth r3_level)))))

theorem normalization_4694 (c1_depth c1_kind c1_sign r3_level : Int) : (¬ (formula_1300 c1_depth c1_kind c1_sign r3_level)) ↔ (¬ (shared_expr_Classification037_129 c1_depth c1_kind c1_sign r3_level)) := (not_congr (normalization_4693 c1_depth c1_kind c1_sign r3_level))

abbrev shared_expr_Classification037_130 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification037_129 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
theorem normalization_4695 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (formula_1301 c1_depth c1_kind c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_130 c1_depth c1_kind c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_4694 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_1616 c1_kind)))

theorem normalization_4696 (c1_depth c1_kind c1_sign r3_group r3_level : Int) : (¬ (formula_1301 c1_depth c1_kind c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification037_130 c1_depth c1_kind c1_sign r3_group r3_level)) := (not_congr (normalization_4695 c1_depth c1_kind c1_sign r3_group r3_level))

theorem normalization_4697 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_1301 c1_depth c1_kind c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification037_130 c1_depth c1_kind c1_sign r3_group r3_level))) := (or_congr (normalization_2568 r3_mode) (or_congr (normalization_2570 r3_mode) (normalization_4696 c1_depth c1_kind c1_sign r3_group r3_level)))

theorem normalization_4698 (c1_depth c1_kind c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_1301 c1_depth c1_kind c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification037_130 c1_depth c1_kind c1_sign r3_group r3_level)))) := (not_congr (normalization_4697 c1_depth c1_kind c1_sign r3_group r3_level r3_mode))

theorem normalization_4699 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4700 (c1_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_4699 c1_depth r3_level))

theorem normalization_4701 (c1_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4702 (c1_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4701 c1_depth r3_level))

abbrev shared_expr_Classification037_131 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_4703 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (formula_1302 c1_depth c1_kind c1_node c1_sign r3_level) ↔ (shared_expr_Classification037_131 c1_depth c1_kind c1_node c1_sign r3_level) := (or_congr (normalization_1588 c1_kind) (or_congr (normalization_1590 c1_kind) (or_congr (normalization_1608 c1_sign) (or_congr (normalization_1640 c1_node) (or_congr (normalization_4700 c1_depth r3_level) (normalization_4702 c1_depth r3_level))))))

theorem normalization_4704 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (¬ (formula_1302 c1_depth c1_kind c1_node c1_sign r3_level)) ↔ (¬ (shared_expr_Classification037_131 c1_depth c1_kind c1_node c1_sign r3_level)) := (not_congr (normalization_4703 c1_depth c1_kind c1_node c1_sign r3_level))

abbrev shared_expr_Classification037_132 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification037_131 c1_depth c1_kind c1_node c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification037_127 c1_depth c1_kind c1_sign r3_level))))
theorem normalization_4705 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1303 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_132 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_4704 c1_depth c1_kind c1_node c1_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_4688 c1_depth c1_kind c1_sign r3_level)))

theorem normalization_4706 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (¬ (formula_1303 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification037_132 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (not_congr (normalization_4705 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

theorem normalization_4707 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_1303 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification037_132 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) := (or_congr (normalization_2578 r3_mode) (or_congr (normalization_2580 r3_mode) (normalization_4706 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))

theorem normalization_4708 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_1303 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification037_132 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) := (not_congr (normalization_4707 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification037_133 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_4709 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (formula_1304 c1_depth c1_kind c1_node c1_sign r3_level) ↔ (shared_expr_Classification037_133 c1_depth c1_kind c1_node c1_sign r3_level) := (or_congr (normalization_1588 c1_kind) (or_congr (normalization_1590 c1_kind) (or_congr (normalization_1608 c1_sign) (or_congr (normalization_1648 c1_node) (or_congr (normalization_4700 c1_depth r3_level) (normalization_4702 c1_depth r3_level))))))

theorem normalization_4710 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (¬ (formula_1304 c1_depth c1_kind c1_node c1_sign r3_level)) ↔ (¬ (shared_expr_Classification037_133 c1_depth c1_kind c1_node c1_sign r3_level)) := (not_congr (normalization_4709 c1_depth c1_kind c1_node c1_sign r3_level))

abbrev shared_expr_Classification037_134 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification037_133 c1_depth c1_kind c1_node c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification037_127 c1_depth c1_kind c1_sign r3_level))))
theorem normalization_4711 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1305 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_134 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_4710 c1_depth c1_kind c1_node c1_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_4688 c1_depth c1_kind c1_sign r3_level)))

theorem normalization_4712 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (¬ (formula_1305 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification037_134 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (not_congr (normalization_4711 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

theorem normalization_4713 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_1305 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification037_134 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) := (or_congr (normalization_2592 r3_mode) (or_congr (normalization_2594 r3_mode) (normalization_4712 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))

theorem normalization_4714 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_1305 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification037_134 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) := (not_congr (normalization_4713 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification037_135 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_4715 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (formula_1306 c1_depth c1_kind c1_node c1_sign r3_level) ↔ (shared_expr_Classification037_135 c1_depth c1_kind c1_node c1_sign r3_level) := (or_congr (normalization_1588 c1_kind) (or_congr (normalization_1590 c1_kind) (or_congr (normalization_1628 c1_sign) (or_congr (normalization_1640 c1_node) (or_congr (normalization_4700 c1_depth r3_level) (normalization_4702 c1_depth r3_level))))))

theorem normalization_4716 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (¬ (formula_1306 c1_depth c1_kind c1_node c1_sign r3_level)) ↔ (¬ (shared_expr_Classification037_135 c1_depth c1_kind c1_node c1_sign r3_level)) := (not_congr (normalization_4715 c1_depth c1_kind c1_node c1_sign r3_level))

abbrev shared_expr_Classification037_136 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification037_129 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification037_135 c1_depth c1_kind c1_node c1_sign r3_level))))
theorem normalization_4717 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1307 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_136 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_4694 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_4716 c1_depth c1_kind c1_node c1_sign r3_level)))

theorem normalization_4718 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (¬ (formula_1307 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification037_136 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (not_congr (normalization_4717 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

theorem normalization_4719 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_1307 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification037_136 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) := (or_congr (normalization_2602 r3_mode) (or_congr (normalization_2603 r3_mode) (normalization_4718 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))

theorem normalization_4720 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_1307 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification037_136 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) := (not_congr (normalization_4719 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification037_137 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_4721 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (formula_1308 c1_depth c1_kind c1_node c1_sign r3_level) ↔ (shared_expr_Classification037_137 c1_depth c1_kind c1_node c1_sign r3_level) := (or_congr (normalization_1588 c1_kind) (or_congr (normalization_1590 c1_kind) (or_congr (normalization_1628 c1_sign) (or_congr (normalization_1648 c1_node) (or_congr (normalization_4700 c1_depth r3_level) (normalization_4702 c1_depth r3_level))))))

theorem normalization_4722 (c1_depth c1_kind c1_node c1_sign r3_level : Int) : (¬ (formula_1308 c1_depth c1_kind c1_node c1_sign r3_level)) ↔ (¬ (shared_expr_Classification037_137 c1_depth c1_kind c1_node c1_sign r3_level)) := (not_congr (normalization_4721 c1_depth c1_kind c1_node c1_sign r3_level))

abbrev shared_expr_Classification037_138 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification037_129 c1_depth c1_kind c1_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification037_137 c1_depth c1_kind c1_node c1_sign r3_level))))
theorem normalization_4723 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (formula_1309 c1_depth c1_kind c1_node c1_sign r3_group r3_level) ↔ (shared_expr_Classification037_138 c1_depth c1_kind c1_node c1_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_4694 c1_depth c1_kind c1_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_4722 c1_depth c1_kind c1_node c1_sign r3_level)))

theorem normalization_4724 (c1_depth c1_kind c1_node c1_sign r3_group r3_level : Int) : (¬ (formula_1309 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification037_138 c1_depth c1_kind c1_node c1_sign r3_group r3_level)) := (not_congr (normalization_4723 c1_depth c1_kind c1_node c1_sign r3_group r3_level))

theorem normalization_4725 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_1309 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification037_138 c1_depth c1_kind c1_node c1_sign r3_group r3_level))) := (or_congr (normalization_2611 r3_mode) (or_congr (normalization_2613 r3_mode) (normalization_4724 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))

theorem normalization_4726 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_1309 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification037_138 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) := (not_congr (normalization_4725 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification037_139 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification037_128 c1_depth c1_kind c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification037_130 c1_depth c1_kind c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification037_132 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification037_134 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification037_136 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification037_138 c1_depth c1_kind c1_node c1_sign r3_group r3_level)))))
theorem normalization_4727 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1310 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_139 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) := (or_congr (normalization_4692 c1_depth c1_kind c1_sign r3_group r3_level r3_mode) (or_congr (normalization_4698 c1_depth c1_kind c1_sign r3_group r3_level r3_mode) (or_congr (normalization_4708 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (or_congr (normalization_4714 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (or_congr (normalization_4720 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (normalization_4726 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))))))

theorem normalization_4728 (c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode : Int) : ((formula_1367 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (formula_1310 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) ↔ ((shared_expr_Classification037_102 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_139 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) := (iff_congr (normalization_4592 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (normalization_4727 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification037_140 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification037_139 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))
theorem normalization_4729 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1383 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_140 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_1523 c1_kind) (normalization_4680 c1_group c1_level c1_mode r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_1523 c1_kind)) (normalization_4727 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)))

abbrev shared_expr_Classification037_141 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification037_103 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_140 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))
theorem normalization_4730 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1384 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_141 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := (iff_congr (normalization_4593 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) (normalization_4729 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_1907 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode : Int) : (formula_1384 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_1095 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode) (shared_expr_Classification037_102 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (shared_expr_Classification037_139 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1525 c1_kind) (replay_591 c1_kind)
  have n1 : ((shared_expr_Classification037_1 c1_group c1_level c1_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Classification037_124 c1_group c1_level c1_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_4682 c1_group c1_level c1_mode r3_group r3_level r3_mode) (replay_1905 c1_group c1_level c1_mode r3_group r3_level r3_mode)
  have n2 : ((shared_expr_Classification037_102 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification037_139 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_4728 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode) (replay_1906 c1_depth c1_kind c1_node c1_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4730 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r3_group r3_level r3_mode) hn

end H4Formal.Generated.Classification
