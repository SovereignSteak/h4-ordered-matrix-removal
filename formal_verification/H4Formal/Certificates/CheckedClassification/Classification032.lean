import H4Formal.BooleanReplaySupport
import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification031

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Classification032_0 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ↔ ((formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True))
abbrev formula_1228 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_0 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_928 (p0 p1 : Prop) : (((p0 ↔ p1)) → ((p0 ↔ True) ↔ (p1 ↔ True))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_1 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
abbrev shared_expr_Classification032_2 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_3 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_2 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification032_4 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_5 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_4 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification032_6 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_7 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((shared_expr_Classification032_6 c2_depth c2_kind c2_sign r2_level) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_8 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_2 c2_depth c2_kind c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_7 c2_depth c2_kind c2_node c2_sign r2_level)))
abbrev shared_expr_Classification032_9 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((shared_expr_Classification032_6 c2_depth c2_kind c2_sign r2_level) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_10 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_2 c2_depth c2_kind c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_9 c2_depth c2_kind c2_node c2_sign r2_level)))
abbrev shared_expr_Classification032_11 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_12 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((shared_expr_Classification032_11 c2_depth c2_kind c2_sign r2_level) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_13 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_12 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_4 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification032_14 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((shared_expr_Classification032_11 c2_depth c2_kind c2_sign r2_level) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_15 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_14 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_4 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification032_16 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((((r2_mode) ≤ (0 : Int)) ∧ (¬ ((r2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_3 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (1 : Int)) ∧ (¬ ((r2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_5 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (2 : Int)) ∧ (¬ ((r2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification032_8 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (3 : Int)) ∧ (¬ ((r2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification032_10 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (4 : Int)) ∧ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification032_13 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (5 : Int)) ∧ (¬ ((r2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification032_15 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))
abbrev shared_expr_Classification032_17 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_16 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))
abbrev shared_expr_Classification032_18 (c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_19 (c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∧ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_20 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_18 c2_level r2_depth r2_kind r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_19 c2_level r2_depth r2_kind r2_sign)))
abbrev shared_expr_Classification032_21 (c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∧ ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_22 (c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_23 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_21 c2_level r2_depth r2_kind r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_22 c2_level r2_depth r2_kind r2_sign)))
abbrev shared_expr_Classification032_24 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_18 c2_level r2_depth r2_kind r2_sign) ∧ ((¬ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_25 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_24 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_26 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_18 c2_level r2_depth r2_kind r2_sign) ∧ ((¬ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_27 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_26 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_28 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_22 c2_level r2_depth r2_kind r2_sign) ∧ ((¬ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_29 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_28 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_30 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_22 c2_level r2_depth r2_kind r2_sign) ∧ ((¬ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_31 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_30 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_32 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_mode) ≤ (0 : Int)) ∧ (¬ ((c2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_20 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ ((((c2_mode) ≤ (1 : Int)) ∧ (¬ ((c2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_23 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ ((((c2_mode) ≤ (2 : Int)) ∧ (¬ ((c2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification032_25 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((((c2_mode) ≤ (3 : Int)) ∧ (¬ ((c2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification032_27 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((((c2_mode) ≤ (4 : Int)) ∧ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification032_29 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((((c2_mode) ≤ (5 : Int)) ∧ (¬ ((c2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification032_31 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))
abbrev shared_expr_Classification032_33 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_34 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int)))) ∧ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_35 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification032_33 c2_node c2_sign h r2_depth r2_node r2_sign) ∨ (shared_expr_Classification032_34 c2_node c2_sign h r2_depth r2_node r2_sign))
abbrev shared_expr_Classification032_36 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
abbrev shared_expr_Classification032_37 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
abbrev shared_expr_Classification032_38 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification032_36 c2_node c2_sign r2_node r2_sign) ∨ (shared_expr_Classification032_37 c2_node c2_sign r2_node r2_sign)))
abbrev shared_expr_Classification032_39 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification032_35 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (shared_expr_Classification032_38 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))
abbrev shared_expr_Classification032_40 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Classification032_39 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))
abbrev shared_expr_Classification032_41 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ True) ∨ (shared_expr_Classification032_40 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign))
abbrev shared_expr_Classification032_42 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_32 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_41 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))
abbrev shared_expr_Classification032_43 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_17 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)) ∨ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_42 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))
theorem normalization_4091 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : ((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ↔ ((shared_expr_Classification032_43 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) := (iff_congr (normalization_4031 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_145))

abbrev shared_expr_Classification032_44 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_45 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_2 c2_depth c2_kind c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_44 c2_depth c2_kind c2_node c2_sign r2_level)))
abbrev shared_expr_Classification032_46 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_47 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_2 c2_depth c2_kind c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_46 c2_depth c2_kind c2_node c2_sign r2_level)))
abbrev shared_expr_Classification032_48 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_49 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_48 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_4 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification032_50 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_51 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_50 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_4 c2_depth c2_kind c2_sign r2_level)))
abbrev shared_expr_Classification032_52 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((((r2_mode) ≤ (0 : Int)) ∧ (¬ ((r2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_3 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (1 : Int)) ∧ (¬ ((r2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_5 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (2 : Int)) ∧ (¬ ((r2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification032_45 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (3 : Int)) ∧ (¬ ((r2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification032_47 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (4 : Int)) ∧ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification032_49 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (5 : Int)) ∧ (¬ ((r2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification032_51 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))
abbrev shared_expr_Classification032_53 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_52 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))
abbrev shared_expr_Classification032_54 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_55 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_54 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_56 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_57 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_56 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_58 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification032_59 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_58 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_60 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification032_61 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_60 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification032_62 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_mode) ≤ (0 : Int)) ∧ (¬ ((c2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_20 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ ((((c2_mode) ≤ (1 : Int)) ∧ (¬ ((c2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_23 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ ((((c2_mode) ≤ (2 : Int)) ∧ (¬ ((c2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification032_55 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((((c2_mode) ≤ (3 : Int)) ∧ (¬ ((c2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification032_57 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((((c2_mode) ≤ (4 : Int)) ∧ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification032_59 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((((c2_mode) ≤ (5 : Int)) ∧ (¬ ((c2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification032_61 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))
abbrev shared_expr_Classification032_63 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (1 : Int)) ∧ (¬ ((r2_sign) ≤ (0 : Int)))) ∨ (((r2_sign) ≤ (2 : Int)) ∧ (¬ ((r2_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification032_64 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification032_36 c2_node c2_sign r2_node r2_sign) ∨ (shared_expr_Classification032_63 c2_node c2_sign r2_node r2_sign)))
abbrev shared_expr_Classification032_65 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_34 c2_node c2_sign h r2_depth r2_node r2_sign) ∨ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification032_33 c2_node c2_sign h r2_depth r2_node r2_sign))
abbrev shared_expr_Classification032_66 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Classification032_64 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ∨ (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification032_65 c2_node c2_sign h r2_depth r2_node r2_sign)))
abbrev shared_expr_Classification032_67 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_62 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_66 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))
abbrev shared_expr_Classification032_68 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_53 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)) ∨ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_67 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))
theorem normalization_4092 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : ((formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ↔ ((shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) := (iff_congr (normalization_4089 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_145))

abbrev shared_expr_Classification032_69 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((shared_expr_Classification032_43 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ↔ ((shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True))
theorem normalization_4093 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1228 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_69 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_4091 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_4092 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification032_70 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_43 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem replay_1574 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1228 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_928 (shared_expr_Classification032_43 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
  have n0 : (shared_expr_Classification032_70 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
    exact Iff.mp (normalization_4090 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_1573 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_4093 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

abbrev shared_expr_Classification032_71 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ↔ (formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_1229 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_71 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_929 (p0 : Prop) : ((p0 ↔ True) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_72 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ↔ (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_4094 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1229 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_72 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_4092 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_4089 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1575 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1229 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_929 (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
  have hn := ht
  exact Iff.mpr (normalization_4094 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

abbrev shared_expr_Classification032_73 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ↔ (formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_1230 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_73 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_930 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_74 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((shared_expr_Classification032_43 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ↔ (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_4095 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1230 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_74 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_4091 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_4089 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of trans.
theorem replay_1576 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1230 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_930 ((shared_expr_Classification032_43 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) ((shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True) (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
  have n0 : (shared_expr_Classification032_69 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
    exact Iff.mp (normalization_4093 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_1574 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)
  have n1 : (shared_expr_Classification032_72 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
    exact Iff.mp (normalization_4094 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_1575 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4095 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

-- Checked replay of mp.
theorem replay_1577 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i136 : ((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : (formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_1576 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) i136

abbrev shared_expr_Classification032_75 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((formula_1225 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (formula_1225 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign))
abbrev formula_1231 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_75 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)

theorem normalized_931 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_76 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_67 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Classification032_67 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign))
theorem normalization_4096 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_1231 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Classification032_76 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := (iff_congr (normalization_4088 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (normalization_4088 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1578 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_1231 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := by
  classical
  have ht := (normalized_931 (shared_expr_Classification032_67 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign))
  have hn := ht
  exact Iff.mpr (normalization_4096 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) hn

abbrev shared_expr_Classification032_77 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_1232 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_77 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_932 (p0 p1 : Prop) : (((p0 ↔ p0)) → (p1 ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_78 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_4097 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_78 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_4089 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_4089 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_1579 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_932 (shared_expr_Classification032_67 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
  have n0 : (shared_expr_Classification032_76 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := by
    exact Iff.mp (normalization_4096 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (replay_1578 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_4097 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

-- Checked replay of mp.
theorem replay_1580 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i136 : ((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : (formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_1579 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_1577 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i136)

theorem normalized_933 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of rewrite.
theorem replay_1581 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_933 (shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
  have hn := ht
  exact Iff.mpr (normalization_4097 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

-- Checked replay of mp.
theorem replay_1582 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i136 : ((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : (formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_1581 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_1580 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i136)

-- Checked replay of mp.
theorem replay_1583 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i136 : ((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : (formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_1579 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_1582 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i136)

-- Checked replay of mp.
theorem replay_1584 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i136 : ((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : (formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_1579 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_1583 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i136)

abbrev shared_expr_Classification032_79 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (((r2_group = (1 : Int)) ∧ (c2_kind = (2 : Int))) ∨ ((¬ (r2_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))))))
abbrev formula_1233 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (shared_expr_Classification032_79 c2_depth c2_kind c2_sign r2_group r2_level)

abbrev shared_expr_Classification032_80 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (((r2_group = (1 : Int)) ∧ (c2_kind = (2 : Int))) ∨ ((¬ (r2_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))))))
abbrev formula_1234 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (shared_expr_Classification032_80 c2_depth c2_kind c2_sign r2_group r2_level)

abbrev shared_expr_Classification032_81 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((r2_group = (1 : Int)) ∧ ((c2_kind = (1 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))))) ∨ ((¬ (r2_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ (c2_depth = r2_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int)))))
abbrev formula_1235 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (shared_expr_Classification032_81 c2_depth c2_kind c2_node c2_sign r2_group r2_level)

abbrev shared_expr_Classification032_82 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((r2_group = (1 : Int)) ∧ ((c2_kind = (1 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))))) ∨ ((¬ (r2_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ (c2_depth = r2_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int)))))
abbrev formula_1236 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (shared_expr_Classification032_82 c2_depth c2_kind c2_node c2_sign r2_group r2_level)

abbrev shared_expr_Classification032_83 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((r2_group = (1 : Int)) ∧ ((c2_kind = (1 : Int)) ∧ (c2_depth = r2_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int)))) ∨ ((¬ (r2_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))))))
abbrev formula_1237 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (shared_expr_Classification032_83 c2_depth c2_kind c2_node c2_sign r2_group r2_level)

abbrev shared_expr_Classification032_84 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((r2_group = (1 : Int)) ∧ ((c2_kind = (1 : Int)) ∧ (c2_depth = r2_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int)))) ∨ ((¬ (r2_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))))))
abbrev formula_1238 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (shared_expr_Classification032_84 c2_depth c2_kind c2_node c2_sign r2_group r2_level)

abbrev shared_expr_Classification032_85 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((r2_mode = (0 : Int)) ∧ (formula_1233 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((r2_mode = (1 : Int)) ∧ (formula_1234 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((r2_mode = (2 : Int)) ∧ (formula_1235 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((r2_mode = (3 : Int)) ∧ (formula_1236 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((r2_mode = (4 : Int)) ∧ (formula_1237 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((r2_mode = (5 : Int)) ∧ (formula_1238 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))
abbrev formula_1239 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification032_85 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)

abbrev shared_expr_Classification032_86 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((c2_kind = (0 : Int)) ∧ ((r2_mode = c2_mode) ∧ (r2_level = c2_level) ∧ (¬ (r2_group = c2_group)))) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_1239 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))
abbrev formula_1240 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification032_86 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)

abbrev shared_expr_Classification032_87 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : Prop := (((c2_group = (1 : Int)) ∧ ((r2_kind = (1 : Int)) ∧ (r2_depth = c2_level) ∧ ((r2_sign = (0 : Int)) ∨ (r2_sign = (2 : Int))))) ∨ ((¬ (c2_group = (1 : Int))) ∧ ((r2_kind = (1 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ∧ ((r2_sign = (0 : Int)) ∨ (r2_sign = (2 : Int))))))
abbrev formula_1241 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Classification032_87 c2_group c2_level r2_depth r2_kind r2_sign)

abbrev shared_expr_Classification032_88 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : Prop := (((c2_group = (1 : Int)) ∧ ((r2_kind = (1 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ∧ ((r2_sign = (1 : Int)) ∨ (r2_sign = (2 : Int))))) ∨ ((¬ (c2_group = (1 : Int))) ∧ ((r2_kind = (1 : Int)) ∧ (r2_depth = c2_level) ∧ ((r2_sign = (1 : Int)) ∨ (r2_sign = (2 : Int))))))
abbrev formula_1242 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Classification032_88 c2_group c2_level r2_depth r2_kind r2_sign)

abbrev shared_expr_Classification032_89 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((c2_mode = (0 : Int)) ∧ (formula_1241 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ ((c2_mode = (1 : Int)) ∧ (formula_1242 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ ((c2_mode = (2 : Int)) ∧ (formula_1217 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((c2_mode = (3 : Int)) ∧ (formula_1218 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((c2_mode = (4 : Int)) ∧ (formula_1219 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((c2_mode = (5 : Int)) ∧ (formula_1220 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))
abbrev formula_1243 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_89 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Classification032_90 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((r2_sign = (0 : Int)) ∧ (c2_sign = (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ ((r2_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r2_depth = h) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ ((r2_sign = (1 : Int)) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))
abbrev formula_1244 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_90 c2_node c2_sign h r2_depth r2_node r2_sign)

abbrev shared_expr_Classification032_91 (c2_node c2_sign r2_node r2_sign : Int) : Prop := ((((r2_sign = (0 : Int)) ∨ (r2_sign = (2 : Int))) ∧ (c2_sign = (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ∨ (((r2_sign = (1 : Int)) ∨ (r2_sign = (2 : Int))) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_1245 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_91 c2_node c2_sign r2_node r2_sign)

abbrev shared_expr_Classification032_92 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((r2_kind = (2 : Int)) ∨ (c2_kind = (2 : Int)) ∨ ((r2_depth = c2_depth) ∧ (formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1245 c2_node c2_sign r2_node r2_sign)))
abbrev formula_1246 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_92 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Classification032_93 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((c2_kind = (0 : Int)) ∧ (formula_1243 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_1246 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))
abbrev formula_1247 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_93 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Classification032_94 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((r2_kind = (0 : Int)) ∧ (formula_1240 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)) ∨ ((¬ (r2_kind = (0 : Int))) ∧ (formula_1247 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))
abbrev formula_1248 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_94 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Classification032_95 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_1226 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_1248 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_1249 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Classification032_95 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

set_option maxHeartbeats 2000000 in
theorem normalized_934 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)) ∨ (((¬ p52) ∧ p53) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p54) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p55))))) ∨ (((¬ p53) ∧ p56) ∧ (((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p59)) ∨ ((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p59)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p60))))))))) ↔ (((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)) ∨ (((¬ p53) ∧ p56) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p59)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p59)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p60)))) ∨ (((¬ p52) ∧ p53) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p54) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p55))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4098 (c2_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ ((¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

abbrev shared_expr_Classification032_96 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
theorem normalization_4099 (c2_depth c2_kind c2_sign r2_level : Int) : ((c2_kind = (1 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (shared_expr_Classification032_96 c2_depth c2_kind c2_sign r2_level) := (and_congr (normalization_660 c2_kind) (and_congr (normalization_4098 c2_depth r2_level) (normalization_664 c2_sign)))

abbrev shared_expr_Classification032_97 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_96 c2_depth c2_kind c2_sign r2_level)))
theorem normalization_4100 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : (formula_1233 c2_depth c2_kind c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_97 c2_depth c2_kind c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_344 r2_group) (normalization_659 c2_kind)) (and_congr (not_congr (normalization_344 r2_group)) (normalization_4099 c2_depth c2_kind c2_sign r2_level)))

theorem normalization_4101 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : ((r2_mode = (0 : Int)) ∧ (formula_1233 c2_depth c2_kind c2_sign r2_group r2_level)) ↔ ((((r2_mode) ≤ (0 : Int)) ∧ (¬ ((r2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_97 c2_depth c2_kind c2_sign r2_group r2_level)) := (and_congr (normalization_354 r2_mode) (normalization_4100 c2_depth c2_kind c2_sign r2_group r2_level))

abbrev shared_expr_Classification032_98 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
theorem normalization_4102 (c2_depth c2_kind c2_sign r2_level : Int) : ((c2_kind = (1 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (shared_expr_Classification032_98 c2_depth c2_kind c2_sign r2_level) := (and_congr (normalization_660 c2_kind) (and_congr (normalization_4098 c2_depth r2_level) (normalization_670 c2_sign)))

abbrev shared_expr_Classification032_99 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_98 c2_depth c2_kind c2_sign r2_level)))
theorem normalization_4103 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : (formula_1234 c2_depth c2_kind c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_99 c2_depth c2_kind c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_344 r2_group) (normalization_659 c2_kind)) (and_congr (not_congr (normalization_344 r2_group)) (normalization_4102 c2_depth c2_kind c2_sign r2_level)))

theorem normalization_4104 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : ((r2_mode = (1 : Int)) ∧ (formula_1234 c2_depth c2_kind c2_sign r2_group r2_level)) ↔ ((((r2_mode) ≤ (1 : Int)) ∧ (¬ ((r2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_99 c2_depth c2_kind c2_sign r2_group r2_level)) := (and_congr (normalization_3772 r2_mode) (normalization_4103 c2_depth c2_kind c2_sign r2_group r2_level))

abbrev shared_expr_Classification032_100 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_96 c2_depth c2_kind c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_44 c2_depth c2_kind c2_node c2_sign r2_level)))
theorem normalization_4105 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (formula_1235 c2_depth c2_kind c2_node c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_100 c2_depth c2_kind c2_node c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_344 r2_group) (normalization_4099 c2_depth c2_kind c2_sign r2_level)) (and_congr (not_congr (normalization_344 r2_group)) (normalization_4042 c2_depth c2_kind c2_node c2_sign r2_level)))

theorem normalization_4106 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((r2_mode = (2 : Int)) ∧ (formula_1235 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ↔ ((((r2_mode) ≤ (2 : Int)) ∧ (¬ ((r2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification032_100 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := (and_congr (normalization_3776 r2_mode) (normalization_4105 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

abbrev shared_expr_Classification032_101 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_96 c2_depth c2_kind c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_46 c2_depth c2_kind c2_node c2_sign r2_level)))
theorem normalization_4107 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (formula_1236 c2_depth c2_kind c2_node c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_101 c2_depth c2_kind c2_node c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_344 r2_group) (normalization_4099 c2_depth c2_kind c2_sign r2_level)) (and_congr (not_congr (normalization_344 r2_group)) (normalization_4045 c2_depth c2_kind c2_node c2_sign r2_level)))

theorem normalization_4108 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((r2_mode = (3 : Int)) ∧ (formula_1236 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ↔ ((((r2_mode) ≤ (3 : Int)) ∧ (¬ ((r2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification032_101 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := (and_congr (normalization_3782 r2_mode) (normalization_4107 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

abbrev shared_expr_Classification032_102 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_48 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_98 c2_depth c2_kind c2_sign r2_level)))
theorem normalization_4109 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (formula_1237 c2_depth c2_kind c2_node c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_102 c2_depth c2_kind c2_node c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_344 r2_group) (normalization_4048 c2_depth c2_kind c2_node c2_sign r2_level)) (and_congr (not_congr (normalization_344 r2_group)) (normalization_4102 c2_depth c2_kind c2_sign r2_level)))

theorem normalization_4110 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((r2_mode = (4 : Int)) ∧ (formula_1237 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ↔ ((((r2_mode) ≤ (4 : Int)) ∧ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification032_102 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := (and_congr (normalization_3786 r2_mode) (normalization_4109 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

abbrev shared_expr_Classification032_103 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_50 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification032_98 c2_depth c2_kind c2_sign r2_level)))
theorem normalization_4111 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (formula_1238 c2_depth c2_kind c2_node c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_103 c2_depth c2_kind c2_node c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_344 r2_group) (normalization_4051 c2_depth c2_kind c2_node c2_sign r2_level)) (and_congr (not_congr (normalization_344 r2_group)) (normalization_4102 c2_depth c2_kind c2_sign r2_level)))

theorem normalization_4112 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((r2_mode = (5 : Int)) ∧ (formula_1238 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ↔ ((((r2_mode) ≤ (5 : Int)) ∧ (¬ ((r2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification032_103 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := (and_congr (normalization_3791 r2_mode) (normalization_4111 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

abbrev shared_expr_Classification032_104 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((((r2_mode) ≤ (0 : Int)) ∧ (¬ ((r2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_97 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (1 : Int)) ∧ (¬ ((r2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_99 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (2 : Int)) ∧ (¬ ((r2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification032_100 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (3 : Int)) ∧ (¬ ((r2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification032_101 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (4 : Int)) ∧ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification032_102 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (5 : Int)) ∧ (¬ ((r2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification032_103 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))
theorem normalization_4113 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1239 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_104 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) := (or_congr (normalization_4101 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (or_congr (normalization_4104 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (or_congr (normalization_4106 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (or_congr (normalization_4108 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (or_congr (normalization_4110 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (normalization_4112 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))))))

abbrev shared_expr_Classification032_105 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_104 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))
theorem normalization_4114 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1240 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_105 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_652 c2_kind) (normalization_4034 c2_group c2_level c2_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_652 c2_kind)) (normalization_4113 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))

theorem normalization_4115 (c2_level r2_depth : Int) : ((r2_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ↔ ((¬ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_4116 (c2_level r2_depth r2_kind r2_sign : Int) : ((r2_kind = (1 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ∧ ((r2_sign = (0 : Int)) ∨ (r2_sign = (2 : Int)))) ↔ (shared_expr_Classification032_19 c2_level r2_depth r2_kind r2_sign) := (and_congr (normalization_148 r2_kind) (and_congr (normalization_4115 c2_level r2_depth) (normalization_3798 r2_sign)))

theorem normalization_4117 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : (formula_1241 c2_group c2_level r2_depth r2_kind r2_sign) ↔ (shared_expr_Classification032_20 c2_group c2_level r2_depth r2_kind r2_sign) := (or_congr (and_congr (normalization_698 c2_group) (normalization_3990 c2_level r2_depth r2_kind r2_sign)) (and_congr (not_congr (normalization_698 c2_group)) (normalization_4116 c2_level r2_depth r2_kind r2_sign)))

theorem normalization_4118 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) : ((c2_mode = (0 : Int)) ∧ (formula_1241 c2_group c2_level r2_depth r2_kind r2_sign)) ↔ ((((c2_mode) ≤ (0 : Int)) ∧ (¬ ((c2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_20 c2_group c2_level r2_depth r2_kind r2_sign)) := (and_congr (normalization_697 c2_mode) (normalization_4117 c2_group c2_level r2_depth r2_kind r2_sign))

theorem normalization_4119 (c2_level r2_depth r2_kind r2_sign : Int) : ((r2_kind = (1 : Int)) ∧ ((r2_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ∧ ((r2_sign = (1 : Int)) ∨ (r2_sign = (2 : Int)))) ↔ (shared_expr_Classification032_21 c2_level r2_depth r2_kind r2_sign) := (and_congr (normalization_148 r2_kind) (and_congr (normalization_4115 c2_level r2_depth) (normalization_3804 r2_sign)))

theorem normalization_4120 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : (formula_1242 c2_group c2_level r2_depth r2_kind r2_sign) ↔ (shared_expr_Classification032_23 c2_group c2_level r2_depth r2_kind r2_sign) := (or_congr (and_congr (normalization_698 c2_group) (normalization_4119 c2_level r2_depth r2_kind r2_sign)) (and_congr (not_congr (normalization_698 c2_group)) (normalization_3996 c2_level r2_depth r2_kind r2_sign)))

theorem normalization_4121 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) : ((c2_mode = (1 : Int)) ∧ (formula_1242 c2_group c2_level r2_depth r2_kind r2_sign)) ↔ ((((c2_mode) ≤ (1 : Int)) ∧ (¬ ((c2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification032_23 c2_group c2_level r2_depth r2_kind r2_sign)) := (and_congr (normalization_709 c2_mode) (normalization_4120 c2_group c2_level r2_depth r2_kind r2_sign))

theorem normalization_4122 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : (formula_1243 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Classification032_62 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) := (or_congr (normalization_4118 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (or_congr (normalization_4121 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (or_congr (normalization_4065 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (or_congr (normalization_4068 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (or_congr (normalization_4071 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (normalization_4074 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign))))))

theorem normalization_4123 (c2_node r2_node : Int) : ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4124 (c2_node c2_sign r2_node r2_sign : Int) : ((r2_sign = (0 : Int)) ∧ (c2_sign = (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_153 r2_sign) (and_congr (normalization_662 c2_sign) (normalization_4123 c2_node r2_node)))

theorem normalization_4125 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((r2_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r2_depth = h) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (shared_expr_Classification032_34 c2_node c2_sign h r2_depth r2_node r2_sign) := (and_congr (normalization_362 r2_sign) (and_congr (normalization_663 c2_sign) (and_congr (normalization_361 h r2_depth) (normalization_4123 c2_node r2_node))))

theorem normalization_4126 (c2_node r2_node : Int) : ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4127 (c2_node r2_node : Int) : (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := (not_congr (normalization_4126 c2_node r2_node))

theorem normalization_4128 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((r2_sign = (1 : Int)) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification032_33 c2_node c2_sign h r2_depth r2_node r2_sign) := (and_congr (normalization_363 r2_sign) (and_congr (normalization_669 c2_sign) (and_congr (normalization_434 h r2_depth) (normalization_4127 c2_node r2_node))))

abbrev shared_expr_Classification032_106 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification032_34 c2_node c2_sign h r2_depth r2_node r2_sign) ∨ (shared_expr_Classification032_33 c2_node c2_sign h r2_depth r2_node r2_sign))
theorem normalization_4129 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign) ↔ (shared_expr_Classification032_106 c2_node c2_sign h r2_depth r2_node r2_sign) := (or_congr (normalization_4124 c2_node c2_sign r2_node r2_sign) (or_congr (normalization_4125 c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4128 c2_node c2_sign h r2_depth r2_node r2_sign)))

theorem normalization_4130 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((r2_depth = c2_depth) ∧ (formula_1244 c2_node c2_sign h r2_depth r2_node r2_sign)) ↔ (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification032_106 c2_node c2_sign h r2_depth r2_node r2_sign)) := (and_congr (normalization_4013 c2_depth r2_depth) (normalization_4129 c2_node c2_sign h r2_depth r2_node r2_sign))

theorem normalization_4131 (c2_depth r2_depth : Int) : ((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ ((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4132 (c2_node r2_node : Int) : ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4133 (c2_node c2_sign r2_node r2_sign : Int) : (((r2_sign = (0 : Int)) ∨ (r2_sign = (2 : Int))) ∧ (c2_sign = (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (shared_expr_Classification032_36 c2_node c2_sign r2_node r2_sign) := (and_congr (normalization_3798 r2_sign) (and_congr (normalization_662 c2_sign) (normalization_4132 c2_node r2_node)))

theorem normalization_4134 (c2_node r2_node : Int) : ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4135 (c2_node r2_node : Int) : (¬ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4134 c2_node r2_node))

theorem normalization_4136 (c2_node c2_sign r2_node r2_sign : Int) : (((r2_sign = (1 : Int)) ∨ (r2_sign = (2 : Int))) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)))) ↔ (shared_expr_Classification032_63 c2_node c2_sign r2_node r2_sign) := (and_congr (normalization_3804 r2_sign) (and_congr (normalization_669 c2_sign) (normalization_4135 c2_node r2_node)))

theorem normalization_4137 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1245 c2_node c2_sign r2_node r2_sign) ↔ ((shared_expr_Classification032_36 c2_node c2_sign r2_node r2_sign) ∨ (shared_expr_Classification032_63 c2_node c2_sign r2_node r2_sign)) := (or_congr (normalization_4133 c2_node c2_sign r2_node r2_sign) (normalization_4136 c2_node c2_sign r2_node r2_sign))

theorem normalization_4138 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1245 c2_node c2_sign r2_node r2_sign)) ↔ (shared_expr_Classification032_64 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) := (and_congr (normalization_4131 c2_depth r2_depth) (normalization_4137 c2_node c2_sign r2_node r2_sign))

abbrev shared_expr_Classification032_107 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∨ (((¬ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification032_106 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (shared_expr_Classification032_64 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))
theorem normalization_4139 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_1246 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Classification032_107 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := (or_congr (normalization_150 r2_kind) (or_congr (normalization_659 c2_kind) (or_congr (normalization_4130 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (normalization_4138 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))))

abbrev shared_expr_Classification032_108 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_62 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_107 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))
theorem normalization_4140 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_1247 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Classification032_108 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := (or_congr (and_congr (normalization_652 c2_kind) (normalization_4122 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) (and_congr (not_congr (normalization_652 c2_kind)) (normalization_4139 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Classification032_109 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification032_105 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)) ∨ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification032_108 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))
theorem normalization_4141 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1248 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_109 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (or_congr (and_congr (normalization_133 r2_kind) (normalization_4114 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_133 r2_kind)) (normalization_4140 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Classification032_110 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Classification032_68 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_109 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_4142 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1249 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Classification032_110 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_4089 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_4141 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_1585 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1249 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_934 ((r2_kind) ≤ (0 : Int)) ((r2_kind) ≤ (-1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_kind) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) ((r2_mode) ≤ (0 : Int)) ((r2_mode) ≤ (-1 : Int)) ((r2_group) ≤ (1 : Int)) ((r2_group) ≤ (0 : Int)) ((c2_kind) ≤ (2 : Int)) ((c2_kind) ≤ (1 : Int)) ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)) ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) ((c2_sign) ≤ (2 : Int)) ((c2_sign) ≤ (1 : Int)) ((r2_mode) ≤ (1 : Int)) ((r2_mode) ≤ (2 : Int)) ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((r2_mode) ≤ (3 : Int)) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int)) ((r2_mode) ≤ (4 : Int)) ((r2_mode) ≤ (5 : Int)) ((c2_mode) ≤ (0 : Int)) ((c2_mode) ≤ (-1 : Int)) ((c2_group) ≤ (1 : Int)) ((c2_group) ≤ (0 : Int)) ((r2_kind) ≤ (1 : Int)) ((c2_level + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r2_sign) ≤ (0 : Int)) ((r2_sign) ≤ (-1 : Int)) ((r2_sign) ≤ (2 : Int)) ((r2_sign) ≤ (1 : Int)) ((c2_level + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ((c2_mode) ≤ (1 : Int)) ((c2_mode) ≤ (2 : Int)) ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ((r2_kind) ≤ (2 : Int)) ((c2_mode) ≤ (3 : Int)) ((((2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * r2_node)) ≤ (-2 : Int)) ((c2_mode) ≤ (4 : Int)) ((c2_mode) ≤ (5 : Int)) ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)) ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4142 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

-- Checked replay of mp.
theorem replay_1586 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i136 : ((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : (formula_1248 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_1585 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_1584 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i136)

theorem normalized_935 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4143 (c2_mode r2_mode : Int) : (r2_mode ≤ c2_mode) ↔ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4144 (c2_mode r2_mode : Int) : (r2_mode ≥ c2_mode) ↔ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_4145 (c2_mode r2_mode : Int) : ((r2_mode ≤ c2_mode) ∧ (r2_mode ≥ c2_mode)) ↔ ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := (and_congr (normalization_4143 c2_mode r2_mode) (normalization_4144 c2_mode r2_mode))

abbrev shared_expr_Classification032_111 (c2_mode r2_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))
theorem normalization_4146 (c2_mode r2_mode : Int) : ((r2_mode = c2_mode) ↔ ((r2_mode ≤ c2_mode) ∧ (r2_mode ≥ c2_mode))) ↔ (shared_expr_Classification032_111 c2_mode r2_mode) := (iff_congr (normalization_3961 c2_mode r2_mode) (normalization_4145 c2_mode r2_mode))

-- Checked replay of rewrite.
theorem replay_1587 (c2_mode r2_mode : Int) : ((r2_mode = c2_mode) ↔ ((r2_mode ≤ c2_mode) ∧ (r2_mode ≥ c2_mode))) := by
  classical
  have ht := (normalized_935 ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4146 c2_mode r2_mode) hn

theorem normalized_936 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4147 (c2_mode r2_mode : Int) : ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ↔ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4148 (c2_mode r2_mode : Int) : ((r2_mode ≤ c2_mode) ↔ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_4143 c2_mode r2_mode) (normalization_4147 c2_mode r2_mode))

-- Checked replay of rewrite.
theorem replay_1588 (c2_mode r2_mode : Int) : ((r2_mode ≤ c2_mode) ↔ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_936 ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4148 c2_mode r2_mode) hn

theorem normalized_937 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4149 (c2_mode r2_mode : Int) : ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_4150 (c2_mode r2_mode : Int) : ((r2_mode ≥ c2_mode) ↔ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := (iff_congr (normalization_4144 c2_mode r2_mode) (normalization_4149 c2_mode r2_mode))

-- Checked replay of rewrite.
theorem replay_1589 (c2_mode r2_mode : Int) : ((r2_mode ≥ c2_mode) ↔ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_937 ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4150 c2_mode r2_mode) hn

theorem normalized_938 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4151 (c2_mode r2_mode : Int) : (((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := (and_congr (normalization_4147 c2_mode r2_mode) (normalization_4149 c2_mode r2_mode))

theorem normalization_4152 (c2_mode r2_mode : Int) : (((r2_mode ≤ c2_mode) ∧ (r2_mode ≥ c2_mode)) ↔ (((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Classification032_111 c2_mode r2_mode) := (iff_congr (normalization_4145 c2_mode r2_mode) (normalization_4151 c2_mode r2_mode))

-- Checked replay of monotonicity.
theorem replay_1590 (c2_mode r2_mode : Int) : (((r2_mode ≤ c2_mode) ∧ (r2_mode ≥ c2_mode)) ↔ (((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_938 ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4148 c2_mode r2_mode) (replay_1588 c2_mode r2_mode)
  have n1 : (((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4150 c2_mode r2_mode) (replay_1589 c2_mode r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4152 c2_mode r2_mode) hn

abbrev shared_expr_Classification032_112 (c2_mode r2_mode : Int) : Prop := ((((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))))
abbrev formula_1250 (c2_mode r2_mode : Int) : Prop := (shared_expr_Classification032_112 c2_mode r2_mode)

theorem normalized_939 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4153 (c2_mode r2_mode : Int) : (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_4147 c2_mode r2_mode))

theorem normalization_4154 (c2_mode r2_mode : Int) : (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := (not_congr (normalization_4149 c2_mode r2_mode))

theorem normalization_4155 (c2_mode r2_mode : Int) : ((¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)))) := (or_congr (normalization_4153 c2_mode r2_mode) (normalization_4154 c2_mode r2_mode))

theorem normalization_4156 (c2_mode r2_mode : Int) : (¬ ((¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))) := (not_congr (normalization_4155 c2_mode r2_mode))

abbrev shared_expr_Classification032_113 (c2_mode r2_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))))
theorem normalization_4157 (c2_mode r2_mode : Int) : (formula_1250 c2_mode r2_mode) ↔ (shared_expr_Classification032_113 c2_mode r2_mode) := (iff_congr (normalization_4151 c2_mode r2_mode) (normalization_4156 c2_mode r2_mode))

-- Checked replay of rewrite.
theorem replay_1591 (c2_mode r2_mode : Int) : (formula_1250 c2_mode r2_mode) := by
  classical
  have ht := (normalized_939 ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4157 c2_mode r2_mode) hn

theorem normalized_940 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4158 (c2_mode r2_mode : Int) : (((r2_mode ≤ c2_mode) ∧ (r2_mode ≥ c2_mode)) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification032_113 c2_mode r2_mode) := (iff_congr (normalization_4145 c2_mode r2_mode) (normalization_4156 c2_mode r2_mode))

-- Checked replay of trans.
theorem replay_1592 (c2_mode r2_mode : Int) : (((r2_mode ≤ c2_mode) ∧ (r2_mode ≥ c2_mode)) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_940 ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) (shared_expr_Classification032_113 c2_mode r2_mode))
  have n0 : (shared_expr_Classification032_111 c2_mode r2_mode) := by
    exact Iff.mp (normalization_4152 c2_mode r2_mode) (replay_1590 c2_mode r2_mode)
  have n1 : (shared_expr_Classification032_113 c2_mode r2_mode) := by
    exact Iff.mp (normalization_4157 c2_mode r2_mode) (replay_1591 c2_mode r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4158 c2_mode r2_mode) hn

theorem normalized_941 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4159 (c2_mode r2_mode : Int) : ((r2_mode = c2_mode) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification032_113 c2_mode r2_mode) := (iff_congr (normalization_3961 c2_mode r2_mode) (normalization_4156 c2_mode r2_mode))

-- Checked replay of trans.
theorem replay_1593 (c2_mode r2_mode : Int) : ((r2_mode = c2_mode) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_941 ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) (shared_expr_Classification032_113 c2_mode r2_mode))
  have n0 : (shared_expr_Classification032_111 c2_mode r2_mode) := by
    exact Iff.mp (normalization_4146 c2_mode r2_mode) (replay_1587 c2_mode r2_mode)
  have n1 : (shared_expr_Classification032_113 c2_mode r2_mode) := by
    exact Iff.mp (normalization_4158 c2_mode r2_mode) (replay_1592 c2_mode r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4159 c2_mode r2_mode) hn

theorem normalized_942 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4160 (c2_level r2_level : Int) : (r2_level ≤ c2_level) ↔ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4161 (c2_level r2_level : Int) : (r2_level ≥ c2_level) ↔ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4162 (c2_level r2_level : Int) : ((r2_level ≤ c2_level) ∧ (r2_level ≥ c2_level)) ↔ ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (and_congr (normalization_4160 c2_level r2_level) (normalization_4161 c2_level r2_level))

abbrev shared_expr_Classification032_114 (c2_level r2_level : Int) : Prop := (((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))
theorem normalization_4163 (c2_level r2_level : Int) : ((r2_level = c2_level) ↔ ((r2_level ≤ c2_level) ∧ (r2_level ≥ c2_level))) ↔ (shared_expr_Classification032_114 c2_level r2_level) := (iff_congr (normalization_3962 c2_level r2_level) (normalization_4162 c2_level r2_level))

-- Checked replay of rewrite.
theorem replay_1594 (c2_level r2_level : Int) : ((r2_level = c2_level) ↔ ((r2_level ≤ c2_level) ∧ (r2_level ≥ c2_level))) := by
  classical
  have ht := (normalized_942 ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4163 c2_level r2_level) hn

theorem normalized_943 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4164 (c2_level r2_level : Int) : ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ↔ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4165 (c2_level r2_level : Int) : ((r2_level ≤ c2_level) ↔ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_4160 c2_level r2_level) (normalization_4164 c2_level r2_level))

-- Checked replay of rewrite.
theorem replay_1595 (c2_level r2_level : Int) : ((r2_level ≤ c2_level) ↔ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_943 ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4165 c2_level r2_level) hn

theorem normalized_944 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4166 (c2_level r2_level : Int) : ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4167 (c2_level r2_level : Int) : ((r2_level ≥ c2_level) ↔ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (iff_congr (normalization_4161 c2_level r2_level) (normalization_4166 c2_level r2_level))

-- Checked replay of rewrite.
theorem replay_1596 (c2_level r2_level : Int) : ((r2_level ≥ c2_level) ↔ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_944 ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4167 c2_level r2_level) hn

theorem normalized_945 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4168 (c2_level r2_level : Int) : (((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (and_congr (normalization_4164 c2_level r2_level) (normalization_4166 c2_level r2_level))

theorem normalization_4169 (c2_level r2_level : Int) : (((r2_level ≤ c2_level) ∧ (r2_level ≥ c2_level)) ↔ (((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ (shared_expr_Classification032_114 c2_level r2_level) := (iff_congr (normalization_4162 c2_level r2_level) (normalization_4168 c2_level r2_level))

-- Checked replay of monotonicity.
theorem replay_1597 (c2_level r2_level : Int) : (((r2_level ≤ c2_level) ∧ (r2_level ≥ c2_level)) ↔ (((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_945 ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4165 c2_level r2_level) (replay_1595 c2_level r2_level)
  have n1 : (((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4167 c2_level r2_level) (replay_1596 c2_level r2_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4169 c2_level r2_level) hn

abbrev shared_expr_Classification032_115 (c2_level r2_level : Int) : Prop := ((((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))))
abbrev formula_1251 (c2_level r2_level : Int) : Prop := (shared_expr_Classification032_115 c2_level r2_level)

theorem normalized_946 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4170 (c2_level r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4164 c2_level r2_level))

theorem normalization_4171 (c2_level r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (not_congr (normalization_4166 c2_level r2_level))

theorem normalization_4172 (c2_level r2_level : Int) : ((¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)))) := (or_congr (normalization_4170 c2_level r2_level) (normalization_4171 c2_level r2_level))

theorem normalization_4173 (c2_level r2_level : Int) : (¬ ((¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))) := (not_congr (normalization_4172 c2_level r2_level))

abbrev shared_expr_Classification032_116 (c2_level r2_level : Int) : Prop := (((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))))
theorem normalization_4174 (c2_level r2_level : Int) : (formula_1251 c2_level r2_level) ↔ (shared_expr_Classification032_116 c2_level r2_level) := (iff_congr (normalization_4168 c2_level r2_level) (normalization_4173 c2_level r2_level))

-- Checked replay of rewrite.
theorem replay_1598 (c2_level r2_level : Int) : (formula_1251 c2_level r2_level) := by
  classical
  have ht := (normalized_946 ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4174 c2_level r2_level) hn

theorem normalized_947 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4175 (c2_level r2_level : Int) : (((r2_level ≤ c2_level) ∧ (r2_level ≥ c2_level)) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification032_116 c2_level r2_level) := (iff_congr (normalization_4162 c2_level r2_level) (normalization_4173 c2_level r2_level))

-- Checked replay of trans.
theorem replay_1599 (c2_level r2_level : Int) : (((r2_level ≤ c2_level) ∧ (r2_level ≥ c2_level)) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_947 ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) (shared_expr_Classification032_116 c2_level r2_level))
  have n0 : (shared_expr_Classification032_114 c2_level r2_level) := by
    exact Iff.mp (normalization_4169 c2_level r2_level) (replay_1597 c2_level r2_level)
  have n1 : (shared_expr_Classification032_116 c2_level r2_level) := by
    exact Iff.mp (normalization_4174 c2_level r2_level) (replay_1598 c2_level r2_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4175 c2_level r2_level) hn

theorem normalized_948 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4176 (c2_level r2_level : Int) : ((r2_level = c2_level) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification032_116 c2_level r2_level) := (iff_congr (normalization_3962 c2_level r2_level) (normalization_4173 c2_level r2_level))

-- Checked replay of trans.
theorem replay_1600 (c2_level r2_level : Int) : ((r2_level = c2_level) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_948 ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) (shared_expr_Classification032_116 c2_level r2_level))
  have n0 : (shared_expr_Classification032_114 c2_level r2_level) := by
    exact Iff.mp (normalization_4163 c2_level r2_level) (replay_1594 c2_level r2_level)
  have n1 : (shared_expr_Classification032_116 c2_level r2_level) := by
    exact Iff.mp (normalization_4175 c2_level r2_level) (replay_1599 c2_level r2_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4176 c2_level r2_level) hn

theorem normalized_949 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4177 (c2_group r2_group : Int) : (r2_group ≤ c2_group) ↔ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4178 (c2_group r2_group : Int) : (r2_group ≥ c2_group) ↔ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_4179 (c2_group r2_group : Int) : ((r2_group ≤ c2_group) ∧ (r2_group ≥ c2_group)) ↔ ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := (and_congr (normalization_4177 c2_group r2_group) (normalization_4178 c2_group r2_group))

abbrev shared_expr_Classification032_117 (c2_group r2_group : Int) : Prop := (((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))
theorem normalization_4180 (c2_group r2_group : Int) : ((r2_group = c2_group) ↔ ((r2_group ≤ c2_group) ∧ (r2_group ≥ c2_group))) ↔ (shared_expr_Classification032_117 c2_group r2_group) := (iff_congr (normalization_4032 c2_group r2_group) (normalization_4179 c2_group r2_group))

-- Checked replay of rewrite.
theorem replay_1601 (c2_group r2_group : Int) : ((r2_group = c2_group) ↔ ((r2_group ≤ c2_group) ∧ (r2_group ≥ c2_group))) := by
  classical
  have ht := (normalized_949 ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4180 c2_group r2_group) hn

theorem normalized_950 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4181 (c2_group r2_group : Int) : ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ↔ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4182 (c2_group r2_group : Int) : ((r2_group ≤ c2_group) ↔ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_4177 c2_group r2_group) (normalization_4181 c2_group r2_group))

-- Checked replay of rewrite.
theorem replay_1602 (c2_group r2_group : Int) : ((r2_group ≤ c2_group) ↔ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_950 ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4182 c2_group r2_group) hn

theorem normalized_951 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4183 (c2_group r2_group : Int) : ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_4184 (c2_group r2_group : Int) : ((r2_group ≥ c2_group) ↔ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := (iff_congr (normalization_4178 c2_group r2_group) (normalization_4183 c2_group r2_group))

-- Checked replay of rewrite.
theorem replay_1603 (c2_group r2_group : Int) : ((r2_group ≥ c2_group) ↔ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_951 ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4184 c2_group r2_group) hn

theorem normalized_952 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4185 (c2_group r2_group : Int) : (((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := (and_congr (normalization_4181 c2_group r2_group) (normalization_4183 c2_group r2_group))

theorem normalization_4186 (c2_group r2_group : Int) : (((r2_group ≤ c2_group) ∧ (r2_group ≥ c2_group)) ↔ (((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ↔ (shared_expr_Classification032_117 c2_group r2_group) := (iff_congr (normalization_4179 c2_group r2_group) (normalization_4185 c2_group r2_group))

-- Checked replay of monotonicity.
theorem replay_1604 (c2_group r2_group : Int) : (((r2_group ≤ c2_group) ∧ (r2_group ≥ c2_group)) ↔ (((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_952 ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4182 c2_group r2_group) (replay_1602 c2_group r2_group)
  have n1 : (((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4184 c2_group r2_group) (replay_1603 c2_group r2_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4186 c2_group r2_group) hn

abbrev shared_expr_Classification032_118 (c2_group r2_group : Int) : Prop := ((((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))
abbrev formula_1252 (c2_group r2_group : Int) : Prop := (shared_expr_Classification032_118 c2_group r2_group)

theorem normalized_953 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4187 (c2_group r2_group : Int) : (¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := (not_congr (normalization_4181 c2_group r2_group))

theorem normalization_4188 (c2_group r2_group : Int) : (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := (not_congr (normalization_4183 c2_group r2_group))

theorem normalization_4189 (c2_group r2_group : Int) : ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))) := (or_congr (normalization_4187 c2_group r2_group) (normalization_4188 c2_group r2_group))

theorem normalization_4190 (c2_group r2_group : Int) : (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))) := (not_congr (normalization_4189 c2_group r2_group))

abbrev shared_expr_Classification032_119 (c2_group r2_group : Int) : Prop := (((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))))
theorem normalization_4191 (c2_group r2_group : Int) : (formula_1252 c2_group r2_group) ↔ (shared_expr_Classification032_119 c2_group r2_group) := (iff_congr (normalization_4185 c2_group r2_group) (normalization_4190 c2_group r2_group))

-- Checked replay of rewrite.
theorem replay_1605 (c2_group r2_group : Int) : (formula_1252 c2_group r2_group) := by
  classical
  have ht := (normalized_953 ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4191 c2_group r2_group) hn

theorem normalized_954 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4192 (c2_group r2_group : Int) : (((r2_group ≤ c2_group) ∧ (r2_group ≥ c2_group)) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification032_119 c2_group r2_group) := (iff_congr (normalization_4179 c2_group r2_group) (normalization_4190 c2_group r2_group))

-- Checked replay of trans.
theorem replay_1606 (c2_group r2_group : Int) : (((r2_group ≤ c2_group) ∧ (r2_group ≥ c2_group)) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_954 ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) (shared_expr_Classification032_119 c2_group r2_group))
  have n0 : (shared_expr_Classification032_117 c2_group r2_group) := by
    exact Iff.mp (normalization_4186 c2_group r2_group) (replay_1604 c2_group r2_group)
  have n1 : (shared_expr_Classification032_119 c2_group r2_group) := by
    exact Iff.mp (normalization_4191 c2_group r2_group) (replay_1605 c2_group r2_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4192 c2_group r2_group) hn

theorem normalized_955 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4193 (c2_group r2_group : Int) : ((r2_group = c2_group) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification032_119 c2_group r2_group) := (iff_congr (normalization_4032 c2_group r2_group) (normalization_4190 c2_group r2_group))

-- Checked replay of trans.
theorem replay_1607 (c2_group r2_group : Int) : ((r2_group = c2_group) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_955 ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) (shared_expr_Classification032_119 c2_group r2_group))
  have n0 : (shared_expr_Classification032_117 c2_group r2_group) := by
    exact Iff.mp (normalization_4180 c2_group r2_group) (replay_1601 c2_group r2_group)
  have n1 : (shared_expr_Classification032_119 c2_group r2_group) := by
    exact Iff.mp (normalization_4192 c2_group r2_group) (replay_1606 c2_group r2_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4193 c2_group r2_group) hn

theorem normalized_956 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4194 (c2_group r2_group : Int) : (¬ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))) := (not_congr (normalization_4190 c2_group r2_group))

abbrev shared_expr_Classification032_120 (c2_group r2_group : Int) : Prop := ((¬ ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))))
theorem normalization_4195 (c2_group r2_group : Int) : ((¬ (r2_group = c2_group)) ↔ (¬ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Classification032_120 c2_group r2_group) := (iff_congr (normalization_4033 c2_group r2_group) (normalization_4194 c2_group r2_group))

-- Checked replay of monotonicity.
theorem replay_1608 (c2_group r2_group : Int) : ((¬ (r2_group = c2_group)) ↔ (¬ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_956 ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification032_119 c2_group r2_group) := by
    exact Iff.mp (normalization_4193 c2_group r2_group) (replay_1607 c2_group r2_group)
  have hn := ht n0
  exact Iff.mpr (normalization_4195 c2_group r2_group) hn

abbrev shared_expr_Classification032_121 (c2_group r2_group : Int) : Prop := ((¬ (¬ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))
abbrev formula_1253 (c2_group r2_group : Int) : Prop := (shared_expr_Classification032_121 c2_group r2_group)

theorem normalized_957 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_122 (c2_group r2_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
theorem normalization_4196 (c2_group r2_group : Int) : (formula_1253 c2_group r2_group) ↔ (shared_expr_Classification032_122 c2_group r2_group) := (iff_congr (normalization_4194 c2_group r2_group) (normalization_4189 c2_group r2_group))

-- Checked replay of rewrite.
theorem replay_1609 (c2_group r2_group : Int) : (formula_1253 c2_group r2_group) := by
  classical
  have ht := (normalized_957 ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4196 c2_group r2_group) hn

theorem normalized_958 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_123 (c2_group r2_group : Int) : Prop := ((¬ ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
theorem normalization_4197 (c2_group r2_group : Int) : ((¬ (r2_group = c2_group)) ↔ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) ↔ (shared_expr_Classification032_123 c2_group r2_group) := (iff_congr (normalization_4033 c2_group r2_group) (normalization_4189 c2_group r2_group))

-- Checked replay of trans.
theorem replay_1610 (c2_group r2_group : Int) : ((¬ (r2_group = c2_group)) ↔ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_958 ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification032_120 c2_group r2_group) := by
    exact Iff.mp (normalization_4195 c2_group r2_group) (replay_1608 c2_group r2_group)
  have n1 : (shared_expr_Classification032_122 c2_group r2_group) := by
    exact Iff.mp (normalization_4196 c2_group r2_group) (replay_1609 c2_group r2_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4197 c2_group r2_group) hn

abbrev shared_expr_Classification032_124 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))) ∧ ((¬ ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))
abbrev formula_1254 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification032_124 c2_group c2_level c2_mode r2_group r2_level r2_mode)

theorem normalized_959 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_125 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
theorem normalization_4198 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : (formula_1254 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_125 c2_group c2_level c2_mode r2_group r2_level r2_mode) := (and_congr (normalization_4156 c2_mode r2_mode) (and_congr (normalization_4173 c2_level r2_level) (normalization_4189 c2_group r2_group)))

theorem normalization_4199 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : (((r2_mode = c2_mode) ∧ (r2_level = c2_level) ∧ (¬ (r2_group = c2_group))) ↔ (formula_1254 c2_group c2_level c2_mode r2_group r2_level r2_mode)) ↔ ((shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_125 c2_group c2_level c2_mode r2_group r2_level r2_mode)) := (iff_congr (normalization_4034 c2_group c2_level c2_mode r2_group r2_level r2_mode) (normalization_4198 c2_group c2_level c2_mode r2_group r2_level r2_mode))

-- Checked replay of monotonicity.
theorem replay_1611 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : (((r2_mode = c2_mode) ∧ (r2_level = c2_level) ∧ (¬ (r2_group = c2_group))) ↔ (formula_1254 c2_group c2_level c2_mode r2_group r2_level r2_mode)) := by
  classical
  have ht := (normalized_959 ((¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ((¬ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)))) ((¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ((¬ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)))) ((¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification032_113 c2_mode r2_mode) := by
    exact Iff.mp (normalization_4159 c2_mode r2_mode) (replay_1593 c2_mode r2_mode)
  have n1 : (shared_expr_Classification032_116 c2_level r2_level) := by
    exact Iff.mp (normalization_4176 c2_level r2_level) (replay_1600 c2_level r2_level)
  have n2 : (shared_expr_Classification032_123 c2_group r2_group) := by
    exact Iff.mp (normalization_4197 c2_group r2_group) (replay_1610 c2_group r2_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4199 c2_group c2_level c2_mode r2_group r2_level r2_mode) hn

theorem normalized_960 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification032_126 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))))
theorem normalization_4200 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : (formula_1183 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode) := (or_congr (normalization_4153 c2_mode r2_mode) (or_congr (normalization_4154 c2_mode r2_mode) (or_congr (normalization_4170 c2_level r2_level) (or_congr (normalization_4171 c2_level r2_level) (normalization_4190 c2_group r2_group)))))

theorem normalization_4201 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : (¬ (formula_1183 c2_group c2_level c2_mode r2_group r2_level r2_mode)) ↔ (¬ (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode)) := (not_congr (normalization_4200 c2_group c2_level c2_mode r2_group r2_level r2_mode))

theorem normalization_4202 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : ((formula_1254 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (¬ (formula_1183 c2_group c2_level c2_mode r2_group r2_level r2_mode))) ↔ ((shared_expr_Classification032_125 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (¬ (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode))) := (iff_congr (normalization_4198 c2_group c2_level c2_mode r2_group r2_level r2_mode) (normalization_4201 c2_group c2_level c2_mode r2_group r2_level r2_mode))

-- Checked replay of rewrite.
theorem replay_1612 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : ((formula_1254 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (¬ (formula_1183 c2_group c2_level c2_mode r2_group r2_level r2_mode))) := by
  classical
  have ht := (normalized_960 ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((¬ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4202 c2_group c2_level c2_mode r2_group r2_level r2_mode) hn

theorem normalized_961 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4203 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : (((r2_mode = c2_mode) ∧ (r2_level = c2_level) ∧ (¬ (r2_group = c2_group))) ↔ (¬ (formula_1183 c2_group c2_level c2_mode r2_group r2_level r2_mode))) ↔ ((shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (¬ (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode))) := (iff_congr (normalization_4034 c2_group c2_level c2_mode r2_group r2_level r2_mode) (normalization_4201 c2_group c2_level c2_mode r2_group r2_level r2_mode))

-- Checked replay of trans.
theorem replay_1613 (c2_group c2_level c2_mode r2_group r2_level r2_mode : Int) : (((r2_mode = c2_mode) ∧ (r2_level = c2_level) ∧ (¬ (r2_group = c2_group))) ↔ (¬ (formula_1183 c2_group c2_level c2_mode r2_group r2_level r2_mode))) := by
  classical
  have ht := (normalized_961 (shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode) (shared_expr_Classification032_125 c2_group c2_level c2_mode r2_group r2_level r2_mode) (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode))
  have n0 : ((shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_125 c2_group c2_level c2_mode r2_group r2_level r2_mode)) := by
    exact Iff.mp (normalization_4199 c2_group c2_level c2_mode r2_group r2_level r2_mode) (replay_1611 c2_group c2_level c2_mode r2_group r2_level r2_mode)
  have n1 : ((shared_expr_Classification032_125 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (¬ (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode))) := by
    exact Iff.mp (normalization_4202 c2_group c2_level c2_mode r2_group r2_level r2_mode) (replay_1612 c2_group c2_level c2_mode r2_group r2_level r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4203 c2_group c2_level c2_mode r2_group r2_level r2_mode) hn

-- Checked replay of rewrite.
theorem replay_1614 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((formula_1239 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) ↔ (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) := by
  classical
  first
  | (simp only [formula_1239, shared_expr_Classification032_85, formula_1233, shared_expr_Classification032_79, formula_1234, shared_expr_Classification032_80, formula_1235, shared_expr_Classification032_81, formula_1236, shared_expr_Classification032_82, formula_1237, shared_expr_Classification032_83, formula_1238, shared_expr_Classification032_84, formula_1182, shared_expr_Classification031_136, formula_1171, shared_expr_Classification031_125, formula_1170, shared_expr_Classification031_124, formula_1173, shared_expr_Classification031_127, formula_1172, shared_expr_Classification031_126, formula_1175, shared_expr_Classification031_129, formula_1174, shared_expr_Classification031_128, formula_1177, shared_expr_Classification031_131, formula_1176, shared_expr_Classification031_130, formula_1179, shared_expr_Classification031_133, formula_1178, shared_expr_Classification031_132, formula_1181, shared_expr_Classification031_135, formula_1180, shared_expr_Classification031_134, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Classification032_127 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∧ (¬ (formula_1183 c2_group c2_level c2_mode r2_group r2_level r2_mode))) ∨ ((¬ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) ∧ (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))
abbrev formula_1255 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification032_127 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)

abbrev shared_expr_Classification032_128 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((formula_1240 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (formula_1255 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))
abbrev formula_1256 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification032_128 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)

theorem normalized_962 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4204 (c2_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_4205 (c2_depth r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) := (not_congr (normalization_4204 c2_depth r2_level))

theorem normalization_4206 (c2_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ↔ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_4207 (c2_depth r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := (not_congr (normalization_4206 c2_depth r2_level))

abbrev shared_expr_Classification032_129 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))
theorem normalization_4208 (c2_depth c2_kind c2_sign r2_level : Int) : (formula_1170 c2_depth c2_kind c2_sign r2_level) ↔ (shared_expr_Classification032_129 c2_depth c2_kind c2_sign r2_level) := (or_congr (normalization_964 c2_kind) (or_congr (normalization_966 c2_kind) (or_congr (normalization_984 c2_sign) (or_congr (normalization_4205 c2_depth r2_level) (normalization_4207 c2_depth r2_level)))))

theorem normalization_4209 (c2_depth c2_kind c2_sign r2_level : Int) : (¬ (formula_1170 c2_depth c2_kind c2_sign r2_level)) ↔ (¬ (shared_expr_Classification032_129 c2_depth c2_kind c2_sign r2_level)) := (not_congr (normalization_4208 c2_depth c2_kind c2_sign r2_level))

abbrev shared_expr_Classification032_130 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification032_129 c2_depth c2_kind c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
theorem normalization_4210 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_130 c2_depth c2_kind c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_4209 c2_depth c2_kind c2_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_992 c2_kind)))

theorem normalization_4211 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification032_130 c2_depth c2_kind c2_sign r2_group r2_level)) := (not_congr (normalization_4210 c2_depth c2_kind c2_sign r2_group r2_level))

theorem normalization_4212 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification032_130 c2_depth c2_kind c2_sign r2_group r2_level))) := (or_congr (normalization_388 r2_mode) (or_congr (normalization_389 r2_mode) (normalization_4211 c2_depth c2_kind c2_sign r2_group r2_level)))

theorem normalization_4213 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification032_130 c2_depth c2_kind c2_sign r2_group r2_level)))) := (not_congr (normalization_4212 c2_depth c2_kind c2_sign r2_group r2_level r2_mode))

theorem normalization_4214 (r2_mode : Int) : (r2_mode ≤ (1 : Int)) ↔ ((r2_mode) ≤ (1 : Int)) := by
  omega

theorem normalization_4215 (r2_mode : Int) : (¬ (r2_mode ≤ (1 : Int))) ↔ (¬ ((r2_mode) ≤ (1 : Int))) := (not_congr (normalization_4214 r2_mode))

theorem normalization_4216 (r2_mode : Int) : (r2_mode ≥ (1 : Int)) ↔ (¬ ((r2_mode) ≤ (0 : Int))) := by
  omega

theorem normalization_4217 (r2_mode : Int) : (¬ (r2_mode ≥ (1 : Int))) ↔ (¬ (¬ ((r2_mode) ≤ (0 : Int)))) := (not_congr (normalization_4216 r2_mode))

abbrev shared_expr_Classification032_131 (c2_depth c2_kind c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))
theorem normalization_4218 (c2_depth c2_kind c2_sign r2_level : Int) : (formula_1172 c2_depth c2_kind c2_sign r2_level) ↔ (shared_expr_Classification032_131 c2_depth c2_kind c2_sign r2_level) := (or_congr (normalization_964 c2_kind) (or_congr (normalization_966 c2_kind) (or_congr (normalization_1008 c2_sign) (or_congr (normalization_4205 c2_depth r2_level) (normalization_4207 c2_depth r2_level)))))

theorem normalization_4219 (c2_depth c2_kind c2_sign r2_level : Int) : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level)) ↔ (¬ (shared_expr_Classification032_131 c2_depth c2_kind c2_sign r2_level)) := (not_congr (normalization_4218 c2_depth c2_kind c2_sign r2_level))

abbrev shared_expr_Classification032_132 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification032_131 c2_depth c2_kind c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
theorem normalization_4220 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_132 c2_depth c2_kind c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_4219 c2_depth c2_kind c2_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_992 c2_kind)))

theorem normalization_4221 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification032_132 c2_depth c2_kind c2_sign r2_group r2_level)) := (not_congr (normalization_4220 c2_depth c2_kind c2_sign r2_group r2_level))

theorem normalization_4222 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification032_132 c2_depth c2_kind c2_sign r2_group r2_level))) := (or_congr (normalization_4215 r2_mode) (or_congr (normalization_4217 r2_mode) (normalization_4221 c2_depth c2_kind c2_sign r2_group r2_level)))

theorem normalization_4223 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification032_132 c2_depth c2_kind c2_sign r2_group r2_level)))) := (not_congr (normalization_4222 c2_depth c2_kind c2_sign r2_group r2_level r2_mode))

theorem normalization_4224 (r2_mode : Int) : (r2_mode ≤ (2 : Int)) ↔ ((r2_mode) ≤ (2 : Int)) := by
  omega

theorem normalization_4225 (r2_mode : Int) : (¬ (r2_mode ≤ (2 : Int))) ↔ (¬ ((r2_mode) ≤ (2 : Int))) := (not_congr (normalization_4224 r2_mode))

theorem normalization_4226 (r2_mode : Int) : (r2_mode ≥ (2 : Int)) ↔ (¬ ((r2_mode) ≤ (1 : Int))) := by
  omega

theorem normalization_4227 (r2_mode : Int) : (¬ (r2_mode ≥ (2 : Int))) ↔ (¬ (¬ ((r2_mode) ≤ (1 : Int)))) := (not_congr (normalization_4226 r2_mode))

theorem normalization_4228 (c2_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4229 (c2_depth r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (not_congr (normalization_4228 c2_depth r2_level))

theorem normalization_4230 (c2_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4231 (c2_depth r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4230 c2_depth r2_level))

abbrev shared_expr_Classification032_133 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
theorem normalization_4232 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level) ↔ (shared_expr_Classification032_133 c2_depth c2_kind c2_node c2_sign r2_level) := (or_congr (normalization_964 c2_kind) (or_congr (normalization_966 c2_kind) (or_congr (normalization_984 c2_sign) (or_congr (normalization_1024 c2_node) (or_congr (normalization_4229 c2_depth r2_level) (normalization_4231 c2_depth r2_level))))))

theorem normalization_4233 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : (¬ (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level)) ↔ (¬ (shared_expr_Classification032_133 c2_depth c2_kind c2_node c2_sign r2_level)) := (not_congr (normalization_4232 c2_depth c2_kind c2_node c2_sign r2_level))

abbrev shared_expr_Classification032_134 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification032_133 c2_depth c2_kind c2_node c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification032_129 c2_depth c2_kind c2_sign r2_level))))
theorem normalization_4234 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_134 c2_depth c2_kind c2_node c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_4233 c2_depth c2_kind c2_node c2_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_4209 c2_depth c2_kind c2_sign r2_level)))

theorem normalization_4235 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification032_134 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := (not_congr (normalization_4234 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

theorem normalization_4236 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification032_134 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := (or_congr (normalization_4225 r2_mode) (or_congr (normalization_4227 r2_mode) (normalization_4235 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))

theorem normalization_4237 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification032_134 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) := (not_congr (normalization_4236 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))

theorem normalization_4238 (r2_mode : Int) : (r2_mode ≤ (3 : Int)) ↔ ((r2_mode) ≤ (3 : Int)) := by
  omega

theorem normalization_4239 (r2_mode : Int) : (¬ (r2_mode ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))) := (not_congr (normalization_4238 r2_mode))

theorem normalization_4240 (r2_mode : Int) : (r2_mode ≥ (3 : Int)) ↔ (¬ ((r2_mode) ≤ (2 : Int))) := by
  omega

theorem normalization_4241 (r2_mode : Int) : (¬ (r2_mode ≥ (3 : Int))) ↔ (¬ (¬ ((r2_mode) ≤ (2 : Int)))) := (not_congr (normalization_4240 r2_mode))

abbrev shared_expr_Classification032_135 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
theorem normalization_4242 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level) ↔ (shared_expr_Classification032_135 c2_depth c2_kind c2_node c2_sign r2_level) := (or_congr (normalization_964 c2_kind) (or_congr (normalization_966 c2_kind) (or_congr (normalization_984 c2_sign) (or_congr (normalization_1036 c2_node) (or_congr (normalization_4229 c2_depth r2_level) (normalization_4231 c2_depth r2_level))))))

theorem normalization_4243 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : (¬ (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level)) ↔ (¬ (shared_expr_Classification032_135 c2_depth c2_kind c2_node c2_sign r2_level)) := (not_congr (normalization_4242 c2_depth c2_kind c2_node c2_sign r2_level))

abbrev shared_expr_Classification032_136 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification032_135 c2_depth c2_kind c2_node c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification032_129 c2_depth c2_kind c2_sign r2_level))))
theorem normalization_4244 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_136 c2_depth c2_kind c2_node c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_4243 c2_depth c2_kind c2_node c2_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_4209 c2_depth c2_kind c2_sign r2_level)))

theorem normalization_4245 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification032_136 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := (not_congr (normalization_4244 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

theorem normalization_4246 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification032_136 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := (or_congr (normalization_4239 r2_mode) (or_congr (normalization_4241 r2_mode) (normalization_4245 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))

theorem normalization_4247 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification032_136 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) := (not_congr (normalization_4246 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))

theorem normalization_4248 (r2_mode : Int) : (r2_mode ≤ (4 : Int)) ↔ ((r2_mode) ≤ (4 : Int)) := by
  omega

theorem normalization_4249 (r2_mode : Int) : (¬ (r2_mode ≤ (4 : Int))) ↔ (¬ ((r2_mode) ≤ (4 : Int))) := (not_congr (normalization_4248 r2_mode))

theorem normalization_4250 (r2_mode : Int) : (¬ (r2_mode ≥ (4 : Int))) ↔ (¬ (¬ ((r2_mode) ≤ (3 : Int)))) := (not_congr (normalization_135 r2_mode))

abbrev shared_expr_Classification032_137 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
theorem normalization_4251 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : (formula_1178 c2_depth c2_kind c2_node c2_sign r2_level) ↔ (shared_expr_Classification032_137 c2_depth c2_kind c2_node c2_sign r2_level) := (or_congr (normalization_964 c2_kind) (or_congr (normalization_966 c2_kind) (or_congr (normalization_1008 c2_sign) (or_congr (normalization_1024 c2_node) (or_congr (normalization_4229 c2_depth r2_level) (normalization_4231 c2_depth r2_level))))))

theorem normalization_4252 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : (¬ (formula_1178 c2_depth c2_kind c2_node c2_sign r2_level)) ↔ (¬ (shared_expr_Classification032_137 c2_depth c2_kind c2_node c2_sign r2_level)) := (not_congr (normalization_4251 c2_depth c2_kind c2_node c2_sign r2_level))

abbrev shared_expr_Classification032_138 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification032_131 c2_depth c2_kind c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification032_137 c2_depth c2_kind c2_node c2_sign r2_level))))
theorem normalization_4253 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_138 c2_depth c2_kind c2_node c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_4219 c2_depth c2_kind c2_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_4252 c2_depth c2_kind c2_node c2_sign r2_level)))

theorem normalization_4254 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification032_138 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := (not_congr (normalization_4253 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

theorem normalization_4255 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification032_138 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := (or_congr (normalization_4249 r2_mode) (or_congr (normalization_4250 r2_mode) (normalization_4254 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))

theorem normalization_4256 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification032_138 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) := (not_congr (normalization_4255 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))

theorem normalization_4257 (r2_mode : Int) : (r2_mode ≤ (5 : Int)) ↔ ((r2_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_4258 (r2_mode : Int) : (¬ (r2_mode ≤ (5 : Int))) ↔ (¬ ((r2_mode) ≤ (5 : Int))) := (not_congr (normalization_4257 r2_mode))

theorem normalization_4259 (r2_mode : Int) : (r2_mode ≥ (5 : Int)) ↔ (¬ ((r2_mode) ≤ (4 : Int))) := by
  omega

theorem normalization_4260 (r2_mode : Int) : (¬ (r2_mode ≥ (5 : Int))) ↔ (¬ (¬ ((r2_mode) ≤ (4 : Int)))) := (not_congr (normalization_4259 r2_mode))

abbrev shared_expr_Classification032_139 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
theorem normalization_4261 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : (formula_1180 c2_depth c2_kind c2_node c2_sign r2_level) ↔ (shared_expr_Classification032_139 c2_depth c2_kind c2_node c2_sign r2_level) := (or_congr (normalization_964 c2_kind) (or_congr (normalization_966 c2_kind) (or_congr (normalization_1008 c2_sign) (or_congr (normalization_1036 c2_node) (or_congr (normalization_4229 c2_depth r2_level) (normalization_4231 c2_depth r2_level))))))

theorem normalization_4262 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : (¬ (formula_1180 c2_depth c2_kind c2_node c2_sign r2_level)) ↔ (¬ (shared_expr_Classification032_139 c2_depth c2_kind c2_node c2_sign r2_level)) := (not_congr (normalization_4261 c2_depth c2_kind c2_node c2_sign r2_level))

abbrev shared_expr_Classification032_140 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification032_131 c2_depth c2_kind c2_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification032_139 c2_depth c2_kind c2_node c2_sign r2_level))))
theorem normalization_4263 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level) ↔ (shared_expr_Classification032_140 c2_depth c2_kind c2_node c2_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_4219 c2_depth c2_kind c2_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_4262 c2_depth c2_kind c2_node c2_sign r2_level)))

theorem normalization_4264 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification032_140 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := (not_congr (normalization_4263 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

theorem normalization_4265 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification032_140 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := (or_congr (normalization_4258 r2_mode) (or_congr (normalization_4260 r2_mode) (normalization_4264 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))

theorem normalization_4266 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification032_140 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) := (not_congr (normalization_4265 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))

abbrev shared_expr_Classification032_141 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ ((r2_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification032_130 c2_depth c2_kind c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification032_132 c2_depth c2_kind c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification032_134 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification032_136 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification032_138 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification032_140 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))))
theorem normalization_4267 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_141 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) := (or_congr (normalization_4213 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (or_congr (normalization_4223 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (or_congr (normalization_4237 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (or_congr (normalization_4247 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (or_congr (normalization_4256 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (normalization_4266 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))))))

theorem normalization_4268 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : ((formula_1239 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) ↔ (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) ↔ ((shared_expr_Classification032_104 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_141 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) := (iff_congr (normalization_4113 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (normalization_4267 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))

abbrev shared_expr_Classification032_142 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode))) ∨ ((¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification032_141 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))
theorem normalization_4269 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1255 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_142 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_890 c2_kind) (normalization_4201 c2_group c2_level c2_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_890 c2_kind)) (normalization_4267 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)))

abbrev shared_expr_Classification032_143 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Classification032_105 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_142 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))
theorem normalization_4270 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1256 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_143 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := (iff_congr (normalization_4114 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) (normalization_4269 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode))

-- Checked replay of monotonicity.
theorem replay_1615 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1256 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := by
  classical
  have ht := (normalized_962 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode) (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode) (shared_expr_Classification032_104 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (shared_expr_Classification032_141 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))
  have n0 : ((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_892 c2_kind) (replay_468 c2_kind)
  have n1 : ((shared_expr_Classification032_1 c2_group c2_level c2_mode r2_group r2_level r2_mode) ↔ (¬ (shared_expr_Classification032_126 c2_group c2_level c2_mode r2_group r2_level r2_mode))) := by
    exact Iff.mp (normalization_4203 c2_group c2_level c2_mode r2_group r2_level r2_mode) (replay_1613 c2_group c2_level c2_mode r2_group r2_level r2_mode)
  have n2 : ((shared_expr_Classification032_104 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification032_141 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) := by
    exact Iff.mp (normalization_4268 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (replay_1614 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4270 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) hn

end H4Formal.Generated.Classification
