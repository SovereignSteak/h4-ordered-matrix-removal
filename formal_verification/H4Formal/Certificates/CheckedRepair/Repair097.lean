import H4Formal.BooleanReplaySupport
import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair096

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair097_0 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ ((formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True))
abbrev formula_2521 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_0 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_2119 (p0 p1 : Prop) : (((p0 ↔ p1)) → ((p0 ↔ True) ↔ (p1 ↔ True))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_1 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
abbrev shared_expr_Repair097_2 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_3 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_2 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Repair097_4 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_5 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_4 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Repair097_6 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_7 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((shared_expr_Repair097_6 c3_depth c3_kind c3_sign r3_level) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_8 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_2 c3_depth c3_kind c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_7 c3_depth c3_kind c3_node c3_sign r3_level)))
abbrev shared_expr_Repair097_9 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((shared_expr_Repair097_6 c3_depth c3_kind c3_sign r3_level) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_10 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_2 c3_depth c3_kind c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_9 c3_depth c3_kind c3_node c3_sign r3_level)))
abbrev shared_expr_Repair097_11 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_12 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((shared_expr_Repair097_11 c3_depth c3_kind c3_sign r3_level) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_13 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_12 c3_depth c3_kind c3_node c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_4 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Repair097_14 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((shared_expr_Repair097_11 c3_depth c3_kind c3_sign r3_level) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_15 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_14 c3_depth c3_kind c3_node c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_4 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Repair097_16 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_3 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_5 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair097_8 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair097_10 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair097_13 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair097_15 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))
abbrev shared_expr_Repair097_17 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair097_16 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Repair097_18 (c3_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_19 (c3_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_20 (c3_group c3_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_18 c3_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_19 c3_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Repair097_21 (c3_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_22 (c3_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_23 (c3_group c3_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_21 c3_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_22 c3_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Repair097_24 (c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Repair097_18 c3_level r3_depth r3_kind r3_sign) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_25 (c3_group c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_24 c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_26 (c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Repair097_18 c3_level r3_depth r3_kind r3_sign) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_27 (c3_group c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_26 c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_28 (c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Repair097_22 c3_level r3_depth r3_kind r3_sign) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_29 (c3_group c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_28 c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_30 (c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Repair097_22 c3_level r3_depth r3_kind r3_sign) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_31 (c3_group c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_30 c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_32 (c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_20 c3_group c3_level r3_depth r3_kind r3_sign)) ∨ ((((c3_mode) ≤ (1 : Int)) ∧ (¬ ((c3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_23 c3_group c3_level r3_depth r3_kind r3_sign)) ∨ ((((c3_mode) ≤ (2 : Int)) ∧ (¬ ((c3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair097_25 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c3_mode) ≤ (3 : Int)) ∧ (¬ ((c3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair097_27 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c3_mode) ≤ (4 : Int)) ∧ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair097_29 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c3_mode) ≤ (5 : Int)) ∧ (¬ ((c3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair097_31 c3_group c3_level r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Repair097_33 (c3_depth c3_kind h r3_kind : Int) : Prop := ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair097_34 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_35 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ∧ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_36 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Repair097_34 c3_node c3_sign h r3_depth r3_node r3_sign) ∨ (shared_expr_Repair097_35 c3_node c3_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair097_37 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (((r3_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
abbrev shared_expr_Repair097_38 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (((r3_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
abbrev shared_expr_Repair097_39 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Repair097_37 c3_node c3_sign r3_node r3_sign) ∨ (shared_expr_Repair097_38 c3_node c3_sign r3_node r3_sign)))
abbrev shared_expr_Repair097_40 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair097_36 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (shared_expr_Repair097_39 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))
abbrev shared_expr_Repair097_41 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Repair097_40 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair097_42 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (¬ (shared_expr_Repair097_33 c3_depth c3_kind h r3_kind))) ∨ (shared_expr_Repair097_41 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))
abbrev shared_expr_Repair097_43 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_32 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair097_42 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Repair097_44 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_17 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair097_43 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))
theorem normalization_7432 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ ((shared_expr_Repair097_44 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) := (iff_congr (normalization_7371 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_305))

abbrev shared_expr_Repair097_45 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_46 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_2 c3_depth c3_kind c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_45 c3_depth c3_kind c3_node c3_sign r3_level)))
abbrev shared_expr_Repair097_47 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_48 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_2 c3_depth c3_kind c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_47 c3_depth c3_kind c3_node c3_sign r3_level)))
abbrev shared_expr_Repair097_49 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_50 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_49 c3_depth c3_kind c3_node c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_4 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Repair097_51 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_52 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_51 c3_depth c3_kind c3_node c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_4 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Repair097_53 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_3 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_5 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair097_46 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair097_48 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair097_50 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair097_52 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))
abbrev shared_expr_Repair097_54 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair097_53 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Repair097_55 (c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_56 (c3_group c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_55 c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_57 (c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_58 (c3_group c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_57 c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_59 (c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair097_60 (c3_group c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_59 c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_61 (c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair097_62 (c3_group c3_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_61 c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair097_63 (c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_20 c3_group c3_level r3_depth r3_kind r3_sign)) ∨ ((((c3_mode) ≤ (1 : Int)) ∧ (¬ ((c3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_23 c3_group c3_level r3_depth r3_kind r3_sign)) ∨ ((((c3_mode) ≤ (2 : Int)) ∧ (¬ ((c3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair097_56 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c3_mode) ≤ (3 : Int)) ∧ (¬ ((c3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair097_58 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c3_mode) ≤ (4 : Int)) ∧ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair097_60 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c3_mode) ≤ (5 : Int)) ∧ (¬ ((c3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair097_62 c3_group c3_level r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Repair097_64 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Repair097_35 c3_node c3_sign h r3_depth r3_node r3_sign) ∨ (shared_expr_Repair097_34 c3_node c3_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair097_65 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair097_66 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Repair097_37 c3_node c3_sign r3_node r3_sign) ∨ (shared_expr_Repair097_65 c3_node c3_sign r3_node r3_sign)))
abbrev shared_expr_Repair097_67 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair097_64 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (shared_expr_Repair097_66 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))
abbrev shared_expr_Repair097_68 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Repair097_67 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair097_69 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (¬ (shared_expr_Repair097_33 c3_depth c3_kind h r3_kind))) ∨ (shared_expr_Repair097_68 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))
abbrev shared_expr_Repair097_70 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_63 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair097_69 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Repair097_71 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_54 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair097_70 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))
theorem normalization_7433 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ ((shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) := (iff_congr (normalization_7430 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_305))

abbrev shared_expr_Repair097_72 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((shared_expr_Repair097_44 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ ((shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True))
theorem normalization_7434 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2521 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_72 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_7432 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_7433 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair097_73 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Repair097_44 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem replay_6296 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2521 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_2119 (shared_expr_Repair097_44 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have n0 : (shared_expr_Repair097_73 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
    exact Iff.mp (normalization_7431 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6295 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_7434 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

abbrev shared_expr_Repair097_74 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ (formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_2522 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_74 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_2120 (p0 : Prop) : ((p0 ↔ True) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_75 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_7435 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2522 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_75 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_7433 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_7430 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_6297 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2522 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_2120 (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7435 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

abbrev shared_expr_Repair097_76 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ (formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_2523 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_76 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_2121 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_77 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((shared_expr_Repair097_44 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ↔ (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_7436 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2523 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_77 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_7432 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_7430 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of trans.
theorem replay_6298 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2523 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_2121 ((shared_expr_Repair097_44 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) ((shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True) (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have n0 : (shared_expr_Repair097_72 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
    exact Iff.mp (normalization_7434 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6296 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have n1 : (shared_expr_Repair097_75 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
    exact Iff.mp (normalization_7435 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6297 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7436 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_6299 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i381 : ((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_6298 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) i381

theorem normalized_2122 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7437 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_2517 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_2517 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)) ↔ ((shared_expr_Repair097_69 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair097_69 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)) := (iff_congr (normalization_7428 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) (normalization_7428 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_6300 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : ((formula_2517 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_2517 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)) := by
  classical
  have ht := (normalized_2122 (shared_expr_Repair097_69 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7437 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) hn

abbrev shared_expr_Repair097_78 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((formula_2518 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (formula_2518 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))
abbrev formula_2524 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_78 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)

theorem normalized_2123 (p0 p1 : Prop) : (((p0 ↔ p0)) → (p1 ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_79 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((shared_expr_Repair097_70 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair097_70 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))
theorem normalization_7438 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_2524 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair097_79 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) := (iff_congr (normalization_7429 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) (normalization_7429 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_6301 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_2524 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) := by
  classical
  have ht := (normalized_2123 (shared_expr_Repair097_69 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Repair097_70 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))
  have n0 : ((shared_expr_Repair097_69 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair097_69 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)) := by
    exact Iff.mp (normalization_7437 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) (replay_6300 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_7438 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) hn

abbrev shared_expr_Repair097_80 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_2525 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_80 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_2124 (p0 p1 : Prop) : (((p0 ↔ p0)) → (p1 ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_81 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_7439 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2525 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_81 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_7430 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_7430 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_6302 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2525 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_2124 (shared_expr_Repair097_70 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have n0 : (shared_expr_Repair097_79 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) := by
    exact Iff.mp (normalization_7438 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) (replay_6301 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_7439 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_6303 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i381 : ((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_6302 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6299 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i381)

theorem normalized_2125 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of rewrite.
theorem replay_6304 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2525 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_2125 (shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7439 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_6305 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i381 : ((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_6304 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6303 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i381)

-- Checked replay of mp.
theorem replay_6306 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i381 : ((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_6302 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6305 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i381)

-- Checked replay of mp.
theorem replay_6307 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i381 : ((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_6302 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6306 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i381)

abbrev shared_expr_Repair097_82 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ (c3_kind = (2 : Int))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2526 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair097_82 c3_depth c3_kind c3_sign r3_group r3_level)

abbrev shared_expr_Repair097_83 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ (c3_kind = (2 : Int))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2527 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair097_83 c3_depth c3_kind c3_sign r3_group r3_level)

abbrev shared_expr_Repair097_84 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r3_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int)))))
abbrev formula_2528 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair097_84 c3_depth c3_kind c3_node c3_sign r3_group r3_level)

abbrev shared_expr_Repair097_85 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r3_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int)))))
abbrev formula_2529 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair097_85 c3_depth c3_kind c3_node c3_sign r3_group r3_level)

abbrev shared_expr_Repair097_86 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r3_level) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int)))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2530 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair097_86 c3_depth c3_kind c3_node c3_sign r3_group r3_level)

abbrev shared_expr_Repair097_87 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r3_level) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int)))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2531 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair097_87 c3_depth c3_kind c3_node c3_sign r3_group r3_level)

abbrev shared_expr_Repair097_88 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((r3_mode = (0 : Int)) ∧ (formula_2526 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((r3_mode = (1 : Int)) ∧ (formula_2527 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((r3_mode = (2 : Int)) ∧ (formula_2528 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((r3_mode = (3 : Int)) ∧ (formula_2529 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((r3_mode = (4 : Int)) ∧ (formula_2530 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((r3_mode = (5 : Int)) ∧ (formula_2531 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))
abbrev formula_2532 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair097_88 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)

abbrev shared_expr_Repair097_89 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((c3_kind = (0 : Int)) ∧ ((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group)))) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2532 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
abbrev formula_2533 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair097_89 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)

abbrev shared_expr_Repair097_90 (c3_group c3_level r3_depth r3_kind r3_sign : Int) : Prop := (((c3_group = (1 : Int)) ∧ ((r3_kind = (1 : Int)) ∧ (r3_depth = c3_level) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))))) ∨ ((¬ (c3_group = (1 : Int))) ∧ ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))))))
abbrev formula_2534 (c3_group c3_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair097_90 c3_group c3_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair097_91 (c3_group c3_level r3_depth r3_kind r3_sign : Int) : Prop := (((c3_group = (1 : Int)) ∧ ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))))) ∨ ((¬ (c3_group = (1 : Int))) ∧ ((r3_kind = (1 : Int)) ∧ (r3_depth = c3_level) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))))))
abbrev formula_2535 (c3_group c3_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair097_91 c3_group c3_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair097_92 (c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((c3_mode = (0 : Int)) ∧ (formula_2534 c3_group c3_level r3_depth r3_kind r3_sign)) ∨ ((c3_mode = (1 : Int)) ∧ (formula_2535 c3_group c3_level r3_depth r3_kind r3_sign)) ∨ ((c3_mode = (2 : Int)) ∧ (formula_2510 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c3_mode = (3 : Int)) ∧ (formula_2511 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c3_mode = (4 : Int)) ∧ (formula_2512 c3_group c3_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c3_mode = (5 : Int)) ∧ (formula_2513 c3_group c3_level r3_depth r3_kind r3_node r3_sign)))
abbrev formula_2536 (c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_92 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair097_93 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ ((r3_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ ((r3_sign = (1 : Int)) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))
abbrev formula_2537 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_93 c3_node c3_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Repair097_94 (c3_node c3_sign r3_node r3_sign : Int) : Prop := ((((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c3_sign = (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ∨ (((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_2538 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_94 c3_node c3_sign r3_node r3_sign)

abbrev shared_expr_Repair097_95 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind = (2 : Int)) ∨ (c3_kind = (2 : Int)))) ∧ (((r3_depth = c3_depth) ∧ (formula_2537 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (((r3_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ (formula_2538 c3_node c3_sign r3_node r3_sign))))
abbrev shared_expr_Repair097_96 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind = (2 : Int)) ∨ (c3_kind = (2 : Int))) ∧ (¬ ((r3_kind = (2 : Int)) ∧ (c3_kind = (1 : Int)) ∧ (c3_depth = h)))) ∨ (shared_expr_Repair097_95 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign))
abbrev formula_2539 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_96 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair097_97 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((c3_kind = (0 : Int)) ∧ (formula_2536 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2539 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_2540 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_97 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair097_98 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((r3_kind = (0 : Int)) ∧ (formula_2533 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)) ∨ ((¬ (r3_kind = (0 : Int))) ∧ (formula_2540 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_2541 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_98 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair097_99 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((formula_2519 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_2541 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_2542 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair097_99 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

set_option maxHeartbeats 2000000 in
theorem normalized_2126 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15))) ∧ (¬ ((p47 ∧ (¬ p35)) ∧ (p15 ∧ (¬ p2)) ∧ (p52 ∧ (¬ p53))))) ∨ ((¬ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)))) ∧ ((((¬ p54) ∧ p55) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p56)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p56)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p59)))) ∨ (((¬ p60) ∧ p54) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p61) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p62)))))))))))) ↔ (((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15))) ∧ (¬ ((p47 ∧ (¬ p35)) ∧ (p15 ∧ (¬ p2)) ∧ (p52 ∧ (¬ p53))))) ∨ ((¬ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)))) ∧ ((((¬ p54) ∧ p55) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p56)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p56)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p59)))) ∨ (((¬ p60) ∧ p54) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p61) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p62))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7440 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ ((¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

abbrev shared_expr_Repair097_100 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
theorem normalization_7441 (c3_depth c3_kind c3_sign r3_level : Int) : ((c3_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (shared_expr_Repair097_100 c3_depth c3_kind c3_sign r3_level) := (and_congr (normalization_6804 c3_kind) (and_congr (normalization_7440 c3_depth r3_level) (normalization_7102 c3_sign)))

abbrev shared_expr_Repair097_101 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_100 c3_depth c3_kind c3_sign r3_level)))
theorem normalization_7442 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (formula_2526 c3_depth c3_kind c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_101 c3_depth c3_kind c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_6806 c3_kind)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_7441 c3_depth c3_kind c3_sign r3_level)))

theorem normalization_7443 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (0 : Int)) ∧ (formula_2526 c3_depth c3_kind c3_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_101 c3_depth c3_kind c3_sign r3_group r3_level)) := (and_congr (normalization_2656 r3_mode) (normalization_7442 c3_depth c3_kind c3_sign r3_group r3_level))

abbrev shared_expr_Repair097_102 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
theorem normalization_7444 (c3_depth c3_kind c3_sign r3_level : Int) : ((c3_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (shared_expr_Repair097_102 c3_depth c3_kind c3_sign r3_level) := (and_congr (normalization_6804 c3_kind) (and_congr (normalization_7440 c3_depth r3_level) (normalization_7106 c3_sign)))

abbrev shared_expr_Repair097_103 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_102 c3_depth c3_kind c3_sign r3_level)))
theorem normalization_7445 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (formula_2527 c3_depth c3_kind c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_103 c3_depth c3_kind c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_6806 c3_kind)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_7444 c3_depth c3_kind c3_sign r3_level)))

theorem normalization_7446 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (1 : Int)) ∧ (formula_2527 c3_depth c3_kind c3_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_103 c3_depth c3_kind c3_sign r3_group r3_level)) := (and_congr (normalization_4009 r3_mode) (normalization_7445 c3_depth c3_kind c3_sign r3_group r3_level))

abbrev shared_expr_Repair097_104 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_100 c3_depth c3_kind c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_45 c3_depth c3_kind c3_node c3_sign r3_level)))
theorem normalization_7447 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2528 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_104 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_7441 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_7382 c3_depth c3_kind c3_node c3_sign r3_level)))

theorem normalization_7448 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (2 : Int)) ∧ (formula_2528 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair097_104 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (and_congr (normalization_4013 r3_mode) (normalization_7447 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

abbrev shared_expr_Repair097_105 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_100 c3_depth c3_kind c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_47 c3_depth c3_kind c3_node c3_sign r3_level)))
theorem normalization_7449 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2529 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_105 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_7441 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_7385 c3_depth c3_kind c3_node c3_sign r3_level)))

theorem normalization_7450 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (3 : Int)) ∧ (formula_2529 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair097_105 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (and_congr (normalization_4019 r3_mode) (normalization_7449 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

abbrev shared_expr_Repair097_106 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_49 c3_depth c3_kind c3_node c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_102 c3_depth c3_kind c3_sign r3_level)))
theorem normalization_7451 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2530 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_106 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_7388 c3_depth c3_kind c3_node c3_sign r3_level)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_7444 c3_depth c3_kind c3_sign r3_level)))

theorem normalization_7452 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (4 : Int)) ∧ (formula_2530 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair097_106 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (and_congr (normalization_4023 r3_mode) (normalization_7451 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

abbrev shared_expr_Repair097_107 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_51 c3_depth c3_kind c3_node c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair097_102 c3_depth c3_kind c3_sign r3_level)))
theorem normalization_7453 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2531 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_107 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_7391 c3_depth c3_kind c3_node c3_sign r3_level)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_7444 c3_depth c3_kind c3_sign r3_level)))

theorem normalization_7454 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (5 : Int)) ∧ (formula_2531 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair097_107 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (and_congr (normalization_4028 r3_mode) (normalization_7453 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

abbrev shared_expr_Repair097_108 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_101 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_103 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair097_104 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair097_105 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair097_106 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair097_107 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))
theorem normalization_7455 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2532 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_108 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) := (or_congr (normalization_7443 c3_depth c3_kind c3_sign r3_group r3_level r3_mode) (or_congr (normalization_7446 c3_depth c3_kind c3_sign r3_group r3_level r3_mode) (or_congr (normalization_7448 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (or_congr (normalization_7450 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (or_congr (normalization_7452 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (normalization_7454 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))))))

abbrev shared_expr_Repair097_109 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair097_108 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
theorem normalization_7456 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2533 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_109 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_6792 c3_kind) (normalization_7374 c3_group c3_level c3_mode r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_6792 c3_kind)) (normalization_7455 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))

theorem normalization_7457 (c3_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_7458 (c3_level r3_depth r3_kind r3_sign : Int) : ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int)))) ↔ (shared_expr_Repair097_19 c3_level r3_depth r3_kind r3_sign) := (and_congr (normalization_1254 r3_kind) (and_congr (normalization_7457 c3_level r3_depth) (normalization_4035 r3_sign)))

theorem normalization_7459 (c3_group c3_level r3_depth r3_kind r3_sign : Int) : (formula_2534 c3_group c3_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair097_20 c3_group c3_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_7130 c3_group) (normalization_7328 c3_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_7130 c3_group)) (normalization_7458 c3_level r3_depth r3_kind r3_sign)))

theorem normalization_7460 (c3_group c3_level c3_mode r3_depth r3_kind r3_sign : Int) : ((c3_mode = (0 : Int)) ∧ (formula_2534 c3_group c3_level r3_depth r3_kind r3_sign)) ↔ ((((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_20 c3_group c3_level r3_depth r3_kind r3_sign)) := (and_congr (normalization_7129 c3_mode) (normalization_7459 c3_group c3_level r3_depth r3_kind r3_sign))

theorem normalization_7461 (c3_level r3_depth r3_kind r3_sign : Int) : ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int)))) ↔ (shared_expr_Repair097_21 c3_level r3_depth r3_kind r3_sign) := (and_congr (normalization_1254 r3_kind) (and_congr (normalization_7457 c3_level r3_depth) (normalization_4041 r3_sign)))

theorem normalization_7462 (c3_group c3_level r3_depth r3_kind r3_sign : Int) : (formula_2535 c3_group c3_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair097_23 c3_group c3_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_7130 c3_group) (normalization_7461 c3_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_7130 c3_group)) (normalization_7334 c3_level r3_depth r3_kind r3_sign)))

theorem normalization_7463 (c3_group c3_level c3_mode r3_depth r3_kind r3_sign : Int) : ((c3_mode = (1 : Int)) ∧ (formula_2535 c3_group c3_level r3_depth r3_kind r3_sign)) ↔ ((((c3_mode) ≤ (1 : Int)) ∧ (¬ ((c3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair097_23 c3_group c3_level r3_depth r3_kind r3_sign)) := (and_congr (normalization_7137 c3_mode) (normalization_7462 c3_group c3_level r3_depth r3_kind r3_sign))

theorem normalization_7464 (c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign : Int) : (formula_2536 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair097_63 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_7460 c3_group c3_level c3_mode r3_depth r3_kind r3_sign) (or_congr (normalization_7463 c3_group c3_level c3_mode r3_depth r3_kind r3_sign) (or_congr (normalization_7405 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_7408 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_7411 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign) (normalization_7414 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign))))))

theorem normalization_7465 (c3_node r3_node : Int) : ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7466 (c3_node c3_sign r3_node r3_sign : Int) : ((r3_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_1259 r3_sign) (and_congr (normalization_7100 c3_sign) (normalization_7465 c3_node r3_node)))

theorem normalization_7467 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : ((r3_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (shared_expr_Repair097_35 c3_node c3_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2664 r3_sign) (and_congr (normalization_7101 c3_sign) (and_congr (normalization_2663 h r3_depth) (normalization_7465 c3_node r3_node))))

theorem normalization_7468 (c3_node r3_node : Int) : ((r3_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) ↔ ((c3_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7469 (c3_node r3_node : Int) : (¬ ((r3_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) := (not_congr (normalization_7468 c3_node r3_node))

theorem normalization_7470 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : ((r3_sign = (1 : Int)) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair097_34 c3_node c3_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2665 r3_sign) (and_congr (normalization_6809 c3_sign) (and_congr (normalization_2736 h r3_depth) (normalization_7469 c3_node r3_node))))

theorem normalization_7471 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : (formula_2537 c3_node c3_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Repair097_64 c3_node c3_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_7466 c3_node c3_sign r3_node r3_sign) (or_congr (normalization_7467 c3_node c3_sign h r3_depth r3_node r3_sign) (normalization_7470 c3_node c3_sign h r3_depth r3_node r3_sign)))

theorem normalization_7472 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : ((r3_depth = c3_depth) ∧ (formula_2537 c3_node c3_sign h r3_depth r3_node r3_sign)) ↔ (((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair097_64 c3_node c3_sign h r3_depth r3_node r3_sign)) := (and_congr (normalization_7353 c3_depth r3_depth) (normalization_7471 c3_node c3_sign h r3_depth r3_node r3_sign))

theorem normalization_7473 (c3_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7474 (c3_node r3_node : Int) : ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r3_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7475 (c3_node c3_sign r3_node r3_sign : Int) : (((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c3_sign = (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (shared_expr_Repair097_37 c3_node c3_sign r3_node r3_sign) := (and_congr (normalization_4035 r3_sign) (and_congr (normalization_7100 c3_sign) (normalization_7474 c3_node r3_node)))

theorem normalization_7476 (c3_node r3_node : Int) : ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7477 (c3_node r3_node : Int) : (¬ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7476 c3_node r3_node))

theorem normalization_7478 (c3_node c3_sign r3_node r3_sign : Int) : (((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))) ↔ (shared_expr_Repair097_65 c3_node c3_sign r3_node r3_sign) := (and_congr (normalization_4041 r3_sign) (and_congr (normalization_6809 c3_sign) (normalization_7477 c3_node r3_node)))

theorem normalization_7479 (c3_node c3_sign r3_node r3_sign : Int) : (formula_2538 c3_node c3_sign r3_node r3_sign) ↔ ((shared_expr_Repair097_37 c3_node c3_sign r3_node r3_sign) ∨ (shared_expr_Repair097_65 c3_node c3_sign r3_node r3_sign)) := (or_congr (normalization_7475 c3_node c3_sign r3_node r3_sign) (normalization_7478 c3_node c3_sign r3_node r3_sign))

theorem normalization_7480 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) : (((r3_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ (formula_2538 c3_node c3_sign r3_node r3_sign)) ↔ (shared_expr_Repair097_66 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) := (and_congr (normalization_7473 c3_depth r3_depth) (normalization_7479 c3_node c3_sign r3_node r3_sign))

theorem normalization_7481 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : (((r3_depth = c3_depth) ∧ (formula_2537 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (((r3_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ (formula_2538 c3_node c3_sign r3_node r3_sign))) ↔ (shared_expr_Repair097_67 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_7472 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) (normalization_7480 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))

theorem normalization_7482 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_2539 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair097_69 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_7350 c3_kind r3_kind) (normalization_7352 c3_depth c3_kind h r3_kind)) (and_congr (not_congr (normalization_7350 c3_kind r3_kind)) (normalization_7481 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)))

theorem normalization_7483 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_2540 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair097_70 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_6792 c3_kind) (normalization_7464 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign)) (and_congr (not_congr (normalization_6792 c3_kind)) (normalization_7482 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Repair097_110 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair097_109 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair097_70 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))
theorem normalization_7484 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2541 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_110 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (and_congr (normalization_1241 r3_kind) (normalization_7456 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_1241 r3_kind)) (normalization_7483 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Repair097_111 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Repair097_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_110 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_7485 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2542 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair097_111 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_7430 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_7484 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_6308 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_2542 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_2126 ((r3_kind) ≤ (0 : Int)) ((r3_kind) ≤ (-1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ((r3_mode) ≤ (0 : Int)) ((r3_mode) ≤ (-1 : Int)) ((r3_group) ≤ (1 : Int)) ((r3_group) ≤ (0 : Int)) ((c3_kind) ≤ (2 : Int)) ((c3_kind) ≤ (1 : Int)) ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)) ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (2 : Int)) ((c3_sign) ≤ (1 : Int)) ((r3_mode) ≤ (1 : Int)) ((r3_mode) ≤ (2 : Int)) ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((r3_mode) ≤ (3 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int)) ((r3_mode) ≤ (4 : Int)) ((r3_mode) ≤ (5 : Int)) ((c3_mode) ≤ (0 : Int)) ((c3_mode) ≤ (-1 : Int)) ((c3_group) ≤ (1 : Int)) ((c3_group) ≤ (0 : Int)) ((r3_kind) ≤ (1 : Int)) ((c3_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)) ((c3_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int)) ((c3_mode) ≤ (1 : Int)) ((c3_mode) ≤ (2 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ((r3_kind) ≤ (2 : Int)) ((c3_mode) ≤ (3 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int)) ((c3_mode) ≤ (4 : Int)) ((c3_mode) ≤ (5 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7485 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_6309 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i381 : ((formula_2499 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_2541 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_6308 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6307 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i381)

theorem normalized_2127 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7486 (c3_mode r3_mode : Int) : (r3_mode ≤ c3_mode) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7487 (c3_mode r3_mode : Int) : (r3_mode ≥ c3_mode) ↔ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_7488 (c3_mode r3_mode : Int) : ((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_7486 c3_mode r3_mode) (normalization_7487 c3_mode r3_mode))

abbrev shared_expr_Repair097_112 (c3_mode r3_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
theorem normalization_7489 (c3_mode r3_mode : Int) : ((r3_mode = c3_mode) ↔ ((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode))) ↔ (shared_expr_Repair097_112 c3_mode r3_mode) := (iff_congr (normalization_7299 c3_mode r3_mode) (normalization_7488 c3_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_6310 (c3_mode r3_mode : Int) : ((r3_mode = c3_mode) ↔ ((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode))) := by
  classical
  have ht := (normalized_2127 ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_7489 c3_mode r3_mode) hn

theorem normalized_2128 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7490 (c3_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7491 (c3_mode r3_mode : Int) : ((r3_mode ≤ c3_mode) ↔ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_7486 c3_mode r3_mode) (normalization_7490 c3_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_6311 (c3_mode r3_mode : Int) : ((r3_mode ≤ c3_mode) ↔ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2128 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7491 c3_mode r3_mode) hn

theorem normalized_2129 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7492 (c3_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_7493 (c3_mode r3_mode : Int) : ((r3_mode ≥ c3_mode) ↔ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (iff_congr (normalization_7487 c3_mode r3_mode) (normalization_7492 c3_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_6312 (c3_mode r3_mode : Int) : ((r3_mode ≥ c3_mode) ↔ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2129 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7493 c3_mode r3_mode) hn

theorem normalized_2130 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7494 (c3_mode r3_mode : Int) : (((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_7490 c3_mode r3_mode) (normalization_7492 c3_mode r3_mode))

theorem normalization_7495 (c3_mode r3_mode : Int) : (((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ (((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Repair097_112 c3_mode r3_mode) := (iff_congr (normalization_7488 c3_mode r3_mode) (normalization_7494 c3_mode r3_mode))

-- Checked replay of monotonicity.
theorem replay_6313 (c3_mode r3_mode : Int) : (((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ (((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2130 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_7491 c3_mode r3_mode) (replay_6311 c3_mode r3_mode)
  have n1 : (((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_7493 c3_mode r3_mode) (replay_6312 c3_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7495 c3_mode r3_mode) hn

abbrev shared_expr_Repair097_113 (c3_mode r3_mode : Int) : Prop := ((((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))))
abbrev formula_2543 (c3_mode r3_mode : Int) : Prop := (shared_expr_Repair097_113 c3_mode r3_mode)

theorem normalized_2131 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7496 (c3_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_7490 c3_mode r3_mode))

theorem normalization_7497 (c3_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (not_congr (normalization_7492 c3_mode r3_mode))

theorem normalization_7498 (c3_mode r3_mode : Int) : ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) := (or_congr (normalization_7496 c3_mode r3_mode) (normalization_7497 c3_mode r3_mode))

theorem normalization_7499 (c3_mode r3_mode : Int) : (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) := (not_congr (normalization_7498 c3_mode r3_mode))

abbrev shared_expr_Repair097_114 (c3_mode r3_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))))
theorem normalization_7500 (c3_mode r3_mode : Int) : (formula_2543 c3_mode r3_mode) ↔ (shared_expr_Repair097_114 c3_mode r3_mode) := (iff_congr (normalization_7494 c3_mode r3_mode) (normalization_7499 c3_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_6314 (c3_mode r3_mode : Int) : (formula_2543 c3_mode r3_mode) := by
  classical
  have ht := (normalized_2131 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7500 c3_mode r3_mode) hn

theorem normalized_2132 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7501 (c3_mode r3_mode : Int) : (((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair097_114 c3_mode r3_mode) := (iff_congr (normalization_7488 c3_mode r3_mode) (normalization_7499 c3_mode r3_mode))

-- Checked replay of trans.
theorem replay_6315 (c3_mode r3_mode : Int) : (((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2132 ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Repair097_114 c3_mode r3_mode))
  have n0 : (shared_expr_Repair097_112 c3_mode r3_mode) := by
    exact Iff.mp (normalization_7495 c3_mode r3_mode) (replay_6313 c3_mode r3_mode)
  have n1 : (shared_expr_Repair097_114 c3_mode r3_mode) := by
    exact Iff.mp (normalization_7500 c3_mode r3_mode) (replay_6314 c3_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7501 c3_mode r3_mode) hn

theorem normalized_2133 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7502 (c3_mode r3_mode : Int) : ((r3_mode = c3_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair097_114 c3_mode r3_mode) := (iff_congr (normalization_7299 c3_mode r3_mode) (normalization_7499 c3_mode r3_mode))

-- Checked replay of trans.
theorem replay_6316 (c3_mode r3_mode : Int) : ((r3_mode = c3_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2133 ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Repair097_114 c3_mode r3_mode))
  have n0 : (shared_expr_Repair097_112 c3_mode r3_mode) := by
    exact Iff.mp (normalization_7489 c3_mode r3_mode) (replay_6310 c3_mode r3_mode)
  have n1 : (shared_expr_Repair097_114 c3_mode r3_mode) := by
    exact Iff.mp (normalization_7501 c3_mode r3_mode) (replay_6315 c3_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7502 c3_mode r3_mode) hn

theorem normalized_2134 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7503 (c3_level r3_level : Int) : (r3_level ≤ c3_level) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7504 (c3_level r3_level : Int) : (r3_level ≥ c3_level) ↔ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_7505 (c3_level r3_level : Int) : ((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_7503 c3_level r3_level) (normalization_7504 c3_level r3_level))

abbrev shared_expr_Repair097_115 (c3_level r3_level : Int) : Prop := (((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
theorem normalization_7506 (c3_level r3_level : Int) : ((r3_level = c3_level) ↔ ((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level))) ↔ (shared_expr_Repair097_115 c3_level r3_level) := (iff_congr (normalization_7300 c3_level r3_level) (normalization_7505 c3_level r3_level))

-- Checked replay of rewrite.
theorem replay_6317 (c3_level r3_level : Int) : ((r3_level = c3_level) ↔ ((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level))) := by
  classical
  have ht := (normalized_2134 ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_7506 c3_level r3_level) hn

theorem normalized_2135 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7507 (c3_level r3_level : Int) : ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7508 (c3_level r3_level : Int) : ((r3_level ≤ c3_level) ↔ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_7503 c3_level r3_level) (normalization_7507 c3_level r3_level))

-- Checked replay of rewrite.
theorem replay_6318 (c3_level r3_level : Int) : ((r3_level ≤ c3_level) ↔ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2135 ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7508 c3_level r3_level) hn

theorem normalized_2136 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7509 (c3_level r3_level : Int) : ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_7510 (c3_level r3_level : Int) : ((r3_level ≥ c3_level) ↔ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (iff_congr (normalization_7504 c3_level r3_level) (normalization_7509 c3_level r3_level))

-- Checked replay of rewrite.
theorem replay_6319 (c3_level r3_level : Int) : ((r3_level ≥ c3_level) ↔ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2136 ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7510 c3_level r3_level) hn

theorem normalized_2137 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7511 (c3_level r3_level : Int) : (((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_7507 c3_level r3_level) (normalization_7509 c3_level r3_level))

theorem normalization_7512 (c3_level r3_level : Int) : (((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ (((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ (shared_expr_Repair097_115 c3_level r3_level) := (iff_congr (normalization_7505 c3_level r3_level) (normalization_7511 c3_level r3_level))

-- Checked replay of monotonicity.
theorem replay_6320 (c3_level r3_level : Int) : (((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ (((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2137 ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_7508 c3_level r3_level) (replay_6318 c3_level r3_level)
  have n1 : (((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_7510 c3_level r3_level) (replay_6319 c3_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7512 c3_level r3_level) hn

abbrev shared_expr_Repair097_116 (c3_level r3_level : Int) : Prop := ((((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))))
abbrev formula_2544 (c3_level r3_level : Int) : Prop := (shared_expr_Repair097_116 c3_level r3_level)

theorem normalized_2138 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7513 (c3_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_7507 c3_level r3_level))

theorem normalization_7514 (c3_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_7509 c3_level r3_level))

theorem normalization_7515 (c3_level r3_level : Int) : ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) := (or_congr (normalization_7513 c3_level r3_level) (normalization_7514 c3_level r3_level))

theorem normalization_7516 (c3_level r3_level : Int) : (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) := (not_congr (normalization_7515 c3_level r3_level))

abbrev shared_expr_Repair097_117 (c3_level r3_level : Int) : Prop := (((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))))
theorem normalization_7517 (c3_level r3_level : Int) : (formula_2544 c3_level r3_level) ↔ (shared_expr_Repair097_117 c3_level r3_level) := (iff_congr (normalization_7511 c3_level r3_level) (normalization_7516 c3_level r3_level))

-- Checked replay of rewrite.
theorem replay_6321 (c3_level r3_level : Int) : (formula_2544 c3_level r3_level) := by
  classical
  have ht := (normalized_2138 ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7517 c3_level r3_level) hn

theorem normalized_2139 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7518 (c3_level r3_level : Int) : (((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair097_117 c3_level r3_level) := (iff_congr (normalization_7505 c3_level r3_level) (normalization_7516 c3_level r3_level))

-- Checked replay of trans.
theorem replay_6322 (c3_level r3_level : Int) : (((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2139 ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Repair097_117 c3_level r3_level))
  have n0 : (shared_expr_Repair097_115 c3_level r3_level) := by
    exact Iff.mp (normalization_7512 c3_level r3_level) (replay_6320 c3_level r3_level)
  have n1 : (shared_expr_Repair097_117 c3_level r3_level) := by
    exact Iff.mp (normalization_7517 c3_level r3_level) (replay_6321 c3_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7518 c3_level r3_level) hn

theorem normalized_2140 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7519 (c3_level r3_level : Int) : ((r3_level = c3_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair097_117 c3_level r3_level) := (iff_congr (normalization_7300 c3_level r3_level) (normalization_7516 c3_level r3_level))

-- Checked replay of trans.
theorem replay_6323 (c3_level r3_level : Int) : ((r3_level = c3_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2140 ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Repair097_117 c3_level r3_level))
  have n0 : (shared_expr_Repair097_115 c3_level r3_level) := by
    exact Iff.mp (normalization_7506 c3_level r3_level) (replay_6317 c3_level r3_level)
  have n1 : (shared_expr_Repair097_117 c3_level r3_level) := by
    exact Iff.mp (normalization_7518 c3_level r3_level) (replay_6322 c3_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7519 c3_level r3_level) hn

theorem normalized_2141 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7520 (c3_group r3_group : Int) : (r3_group ≤ c3_group) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7521 (c3_group r3_group : Int) : (r3_group ≥ c3_group) ↔ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_7522 (c3_group r3_group : Int) : ((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_7520 c3_group r3_group) (normalization_7521 c3_group r3_group))

abbrev shared_expr_Repair097_118 (c3_group r3_group : Int) : Prop := (((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
theorem normalization_7523 (c3_group r3_group : Int) : ((r3_group = c3_group) ↔ ((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group))) ↔ (shared_expr_Repair097_118 c3_group r3_group) := (iff_congr (normalization_7372 c3_group r3_group) (normalization_7522 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6324 (c3_group r3_group : Int) : ((r3_group = c3_group) ↔ ((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group))) := by
  classical
  have ht := (normalized_2141 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_7523 c3_group r3_group) hn

theorem normalized_2142 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7524 (c3_group r3_group : Int) : ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7525 (c3_group r3_group : Int) : ((r3_group ≤ c3_group) ↔ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_7520 c3_group r3_group) (normalization_7524 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6325 (c3_group r3_group : Int) : ((r3_group ≤ c3_group) ↔ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2142 ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7525 c3_group r3_group) hn

theorem normalized_2143 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7526 (c3_group r3_group : Int) : ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_7527 (c3_group r3_group : Int) : ((r3_group ≥ c3_group) ↔ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (iff_congr (normalization_7521 c3_group r3_group) (normalization_7526 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6326 (c3_group r3_group : Int) : ((r3_group ≥ c3_group) ↔ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2143 ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7527 c3_group r3_group) hn

theorem normalized_2144 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7528 (c3_group r3_group : Int) : (((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_7524 c3_group r3_group) (normalization_7526 c3_group r3_group))

theorem normalization_7529 (c3_group r3_group : Int) : (((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ (((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ↔ (shared_expr_Repair097_118 c3_group r3_group) := (iff_congr (normalization_7522 c3_group r3_group) (normalization_7528 c3_group r3_group))

-- Checked replay of monotonicity.
theorem replay_6327 (c3_group r3_group : Int) : (((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ (((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2144 ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_7525 c3_group r3_group) (replay_6325 c3_group r3_group)
  have n1 : (((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_7527 c3_group r3_group) (replay_6326 c3_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7529 c3_group r3_group) hn

abbrev shared_expr_Repair097_119 (c3_group r3_group : Int) : Prop := ((((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))
abbrev formula_2545 (c3_group r3_group : Int) : Prop := (shared_expr_Repair097_119 c3_group r3_group)

theorem normalized_2145 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7530 (c3_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_7524 c3_group r3_group))

theorem normalization_7531 (c3_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (not_congr (normalization_7526 c3_group r3_group))

theorem normalization_7532 (c3_group r3_group : Int) : ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) := (or_congr (normalization_7530 c3_group r3_group) (normalization_7531 c3_group r3_group))

theorem normalization_7533 (c3_group r3_group : Int) : (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))) := (not_congr (normalization_7532 c3_group r3_group))

abbrev shared_expr_Repair097_120 (c3_group r3_group : Int) : Prop := (((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_7534 (c3_group r3_group : Int) : (formula_2545 c3_group r3_group) ↔ (shared_expr_Repair097_120 c3_group r3_group) := (iff_congr (normalization_7528 c3_group r3_group) (normalization_7533 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6328 (c3_group r3_group : Int) : (formula_2545 c3_group r3_group) := by
  classical
  have ht := (normalized_2145 ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7534 c3_group r3_group) hn

theorem normalized_2146 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7535 (c3_group r3_group : Int) : (((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair097_120 c3_group r3_group) := (iff_congr (normalization_7522 c3_group r3_group) (normalization_7533 c3_group r3_group))

-- Checked replay of trans.
theorem replay_6329 (c3_group r3_group : Int) : (((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2146 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Repair097_120 c3_group r3_group))
  have n0 : (shared_expr_Repair097_118 c3_group r3_group) := by
    exact Iff.mp (normalization_7529 c3_group r3_group) (replay_6327 c3_group r3_group)
  have n1 : (shared_expr_Repair097_120 c3_group r3_group) := by
    exact Iff.mp (normalization_7534 c3_group r3_group) (replay_6328 c3_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7535 c3_group r3_group) hn

theorem normalized_2147 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7536 (c3_group r3_group : Int) : ((r3_group = c3_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair097_120 c3_group r3_group) := (iff_congr (normalization_7372 c3_group r3_group) (normalization_7533 c3_group r3_group))

-- Checked replay of trans.
theorem replay_6330 (c3_group r3_group : Int) : ((r3_group = c3_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2147 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Repair097_120 c3_group r3_group))
  have n0 : (shared_expr_Repair097_118 c3_group r3_group) := by
    exact Iff.mp (normalization_7523 c3_group r3_group) (replay_6324 c3_group r3_group)
  have n1 : (shared_expr_Repair097_120 c3_group r3_group) := by
    exact Iff.mp (normalization_7535 c3_group r3_group) (replay_6329 c3_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7536 c3_group r3_group) hn

theorem normalized_2148 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7537 (c3_group r3_group : Int) : (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) := (not_congr (normalization_7533 c3_group r3_group))

abbrev shared_expr_Repair097_121 (c3_group r3_group : Int) : Prop := ((¬ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))))
theorem normalization_7538 (c3_group r3_group : Int) : ((¬ (r3_group = c3_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Repair097_121 c3_group r3_group) := (iff_congr (normalization_7373 c3_group r3_group) (normalization_7537 c3_group r3_group))

-- Checked replay of monotonicity.
theorem replay_6331 (c3_group r3_group : Int) : ((¬ (r3_group = c3_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_2148 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair097_120 c3_group r3_group) := by
    exact Iff.mp (normalization_7536 c3_group r3_group) (replay_6330 c3_group r3_group)
  have hn := ht n0
  exact Iff.mpr (normalization_7538 c3_group r3_group) hn

abbrev shared_expr_Repair097_122 (c3_group r3_group : Int) : Prop := ((¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2546 (c3_group r3_group : Int) : Prop := (shared_expr_Repair097_122 c3_group r3_group)

theorem normalized_2149 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_123 (c3_group r3_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_7539 (c3_group r3_group : Int) : (formula_2546 c3_group r3_group) ↔ (shared_expr_Repair097_123 c3_group r3_group) := (iff_congr (normalization_7537 c3_group r3_group) (normalization_7532 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6332 (c3_group r3_group : Int) : (formula_2546 c3_group r3_group) := by
  classical
  have ht := (normalized_2149 ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7539 c3_group r3_group) hn

theorem normalized_2150 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_124 (c3_group r3_group : Int) : Prop := ((¬ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_7540 (c3_group r3_group : Int) : ((¬ (r3_group = c3_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) ↔ (shared_expr_Repair097_124 c3_group r3_group) := (iff_congr (normalization_7373 c3_group r3_group) (normalization_7532 c3_group r3_group))

-- Checked replay of trans.
theorem replay_6333 (c3_group r3_group : Int) : ((¬ (r3_group = c3_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_2150 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair097_121 c3_group r3_group) := by
    exact Iff.mp (normalization_7538 c3_group r3_group) (replay_6331 c3_group r3_group)
  have n1 : (shared_expr_Repair097_123 c3_group r3_group) := by
    exact Iff.mp (normalization_7539 c3_group r3_group) (replay_6332 c3_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7540 c3_group r3_group) hn

abbrev shared_expr_Repair097_125 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ∧ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2547 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair097_125 c3_group c3_level c3_mode r3_group r3_level r3_mode)

theorem normalized_2151 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_126 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_7541 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (formula_2547 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_126 c3_group c3_level c3_mode r3_group r3_level r3_mode) := (and_congr (normalization_7499 c3_mode r3_mode) (and_congr (normalization_7516 c3_level r3_level) (normalization_7532 c3_group r3_group)))

theorem normalization_7542 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group))) ↔ (formula_2547 c3_group c3_level c3_mode r3_group r3_level r3_mode)) ↔ ((shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_126 c3_group c3_level c3_mode r3_group r3_level r3_mode)) := (iff_congr (normalization_7374 c3_group c3_level c3_mode r3_group r3_level r3_mode) (normalization_7541 c3_group c3_level c3_mode r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_6334 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group))) ↔ (formula_2547 c3_group c3_level c3_mode r3_group r3_level r3_mode)) := by
  classical
  have ht := (normalized_2151 ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair097_114 c3_mode r3_mode) := by
    exact Iff.mp (normalization_7502 c3_mode r3_mode) (replay_6316 c3_mode r3_mode)
  have n1 : (shared_expr_Repair097_117 c3_level r3_level) := by
    exact Iff.mp (normalization_7519 c3_level r3_level) (replay_6323 c3_level r3_level)
  have n2 : (shared_expr_Repair097_124 c3_group r3_group) := by
    exact Iff.mp (normalization_7540 c3_group r3_group) (replay_6333 c3_group r3_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_7542 c3_group c3_level c3_mode r3_group r3_level r3_mode) hn

theorem normalized_2152 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair097_127 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_7543 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (formula_2476 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode) := (or_congr (normalization_7496 c3_mode r3_mode) (or_congr (normalization_7497 c3_mode r3_mode) (or_congr (normalization_7513 c3_level r3_level) (or_congr (normalization_7514 c3_level r3_level) (normalization_7533 c3_group r3_group)))))

theorem normalization_7544 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (¬ (formula_2476 c3_group c3_level c3_mode r3_group r3_level r3_mode)) ↔ (¬ (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode)) := (not_congr (normalization_7543 c3_group c3_level c3_mode r3_group r3_level r3_mode))

theorem normalization_7545 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : ((formula_2547 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (formula_2476 c3_group c3_level c3_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Repair097_126 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_7541 c3_group c3_level c3_mode r3_group r3_level r3_mode) (normalization_7544 c3_group c3_level c3_mode r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_6335 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : ((formula_2547 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (formula_2476 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_2152 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7545 c3_group c3_level c3_mode r3_group r3_level r3_mode) hn

theorem normalized_2153 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7546 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group))) ↔ (¬ (formula_2476 c3_group c3_level c3_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_7374 c3_group c3_level c3_mode r3_group r3_level r3_mode) (normalization_7544 c3_group c3_level c3_mode r3_group r3_level r3_mode))

-- Checked replay of trans.
theorem replay_6336 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group))) ↔ (¬ (formula_2476 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_2153 (shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Repair097_126 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode))
  have n0 : ((shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_126 c3_group c3_level c3_mode r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_7542 c3_group c3_level c3_mode r3_group r3_level r3_mode) (replay_6334 c3_group c3_level c3_mode r3_group r3_level r3_mode)
  have n1 : ((shared_expr_Repair097_126 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_7545 c3_group c3_level c3_mode r3_group r3_level r3_mode) (replay_6335 c3_group c3_level c3_mode r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7546 c3_group c3_level c3_mode r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_6337 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((formula_2532 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (formula_2475 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) := by
  classical
  first
  | (simp only [formula_2532, shared_expr_Repair097_88, formula_2526, shared_expr_Repair097_82, formula_2527, shared_expr_Repair097_83, formula_2528, shared_expr_Repair097_84, formula_2529, shared_expr_Repair097_85, formula_2530, shared_expr_Repair097_86, formula_2531, shared_expr_Repair097_87, formula_2475, shared_expr_Repair096_36, formula_2464, shared_expr_Repair096_25, formula_2463, shared_expr_Repair096_24, formula_2466, shared_expr_Repair096_27, formula_2465, shared_expr_Repair096_26, formula_2468, shared_expr_Repair096_29, formula_2467, shared_expr_Repair096_28, formula_2470, shared_expr_Repair096_31, formula_2469, shared_expr_Repair096_30, formula_2472, shared_expr_Repair096_33, formula_2471, shared_expr_Repair096_32, formula_2474, shared_expr_Repair096_35, formula_2473, shared_expr_Repair096_34, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Repair097_128 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∧ (¬ (formula_2476 c3_group c3_level c3_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ∧ (formula_2475 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
abbrev formula_2548 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair097_128 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)

abbrev shared_expr_Repair097_129 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_2533 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (formula_2548 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
abbrev formula_2549 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair097_129 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)

theorem normalized_2154 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7547 (c3_sign : Int) : (c3_sign ≤ (0 : Int)) ↔ ((c3_sign) ≤ (0 : Int)) := by
  omega

theorem normalization_7548 (c3_sign : Int) : (¬ (c3_sign ≤ (0 : Int))) ↔ (¬ ((c3_sign) ≤ (0 : Int))) := (not_congr (normalization_7547 c3_sign))

theorem normalization_7549 (c3_sign : Int) : (c3_sign ≥ (0 : Int)) ↔ (¬ ((c3_sign) ≤ (-1 : Int))) := by
  omega

theorem normalization_7550 (c3_sign : Int) : (¬ (c3_sign ≥ (0 : Int))) ↔ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) := (not_congr (normalization_7549 c3_sign))

theorem normalization_7551 (c3_sign : Int) : ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))) ↔ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))) := (or_congr (normalization_7548 c3_sign) (normalization_7550 c3_sign))

theorem normalization_7552 (c3_sign : Int) : (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ↔ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) := (not_congr (normalization_7551 c3_sign))

theorem normalization_7553 (c3_sign : Int) : (c3_sign ≤ (2 : Int)) ↔ ((c3_sign) ≤ (2 : Int)) := by
  omega

theorem normalization_7554 (c3_sign : Int) : (¬ (c3_sign ≤ (2 : Int))) ↔ (¬ ((c3_sign) ≤ (2 : Int))) := (not_congr (normalization_7553 c3_sign))

theorem normalization_7555 (c3_sign : Int) : (c3_sign ≥ (2 : Int)) ↔ (¬ ((c3_sign) ≤ (1 : Int))) := by
  omega

theorem normalization_7556 (c3_sign : Int) : (¬ (c3_sign ≥ (2 : Int))) ↔ (¬ (¬ ((c3_sign) ≤ (1 : Int)))) := (not_congr (normalization_7555 c3_sign))

theorem normalization_7557 (c3_sign : Int) : ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))) ↔ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))) := (or_congr (normalization_7554 c3_sign) (normalization_7556 c3_sign))

theorem normalization_7558 (c3_sign : Int) : (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))) ↔ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))) := (not_congr (normalization_7557 c3_sign))

theorem normalization_7559 (c3_sign : Int) : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) := (or_congr (normalization_7552 c3_sign) (normalization_7558 c3_sign))

theorem normalization_7560 (c3_sign : Int) : (¬ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_7559 c3_sign))

theorem normalization_7561 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_7562 (c3_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) := (not_congr (normalization_7561 c3_depth r3_level))

theorem normalization_7563 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_7564 (c3_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := (not_congr (normalization_7563 c3_depth r3_level))

abbrev shared_expr_Repair097_130 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_7565 (c3_depth c3_kind c3_sign r3_level : Int) : (formula_2463 c3_depth c3_kind c3_sign r3_level) ↔ (shared_expr_Repair097_130 c3_depth c3_kind c3_sign r3_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7560 c3_sign) (or_congr (normalization_7562 c3_depth r3_level) (normalization_7564 c3_depth r3_level)))))

theorem normalization_7566 (c3_depth c3_kind c3_sign r3_level : Int) : (¬ (formula_2463 c3_depth c3_kind c3_sign r3_level)) ↔ (¬ (shared_expr_Repair097_130 c3_depth c3_kind c3_sign r3_level)) := (not_congr (normalization_7565 c3_depth c3_kind c3_sign r3_level))

abbrev shared_expr_Repair097_131 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair097_130 c3_depth c3_kind c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
theorem normalization_7567 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (formula_2464 c3_depth c3_kind c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_131 c3_depth c3_kind c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_7566 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_6942 c3_kind)))

theorem normalization_7568 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (¬ (formula_2464 c3_depth c3_kind c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair097_131 c3_depth c3_kind c3_sign r3_group r3_level)) := (not_congr (normalization_7567 c3_depth c3_kind c3_sign r3_group r3_level))

theorem normalization_7569 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_2464 c3_depth c3_kind c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair097_131 c3_depth c3_kind c3_sign r3_group r3_level))) := (or_congr (normalization_2690 r3_mode) (or_congr (normalization_2691 r3_mode) (normalization_7568 c3_depth c3_kind c3_sign r3_group r3_level)))

theorem normalization_7570 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_2464 c3_depth c3_kind c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair097_131 c3_depth c3_kind c3_sign r3_group r3_level)))) := (not_congr (normalization_7569 c3_depth c3_kind c3_sign r3_group r3_level r3_mode))

theorem normalization_7571 (c3_sign : Int) : ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) := (or_congr (normalization_6992 c3_sign) (normalization_7558 c3_sign))

theorem normalization_7572 (c3_sign : Int) : (¬ ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_7571 c3_sign))

abbrev shared_expr_Repair097_132 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_7573 (c3_depth c3_kind c3_sign r3_level : Int) : (formula_2465 c3_depth c3_kind c3_sign r3_level) ↔ (shared_expr_Repair097_132 c3_depth c3_kind c3_sign r3_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7572 c3_sign) (or_congr (normalization_7562 c3_depth r3_level) (normalization_7564 c3_depth r3_level)))))

theorem normalization_7574 (c3_depth c3_kind c3_sign r3_level : Int) : (¬ (formula_2465 c3_depth c3_kind c3_sign r3_level)) ↔ (¬ (shared_expr_Repair097_132 c3_depth c3_kind c3_sign r3_level)) := (not_congr (normalization_7573 c3_depth c3_kind c3_sign r3_level))

abbrev shared_expr_Repair097_133 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair097_132 c3_depth c3_kind c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
theorem normalization_7575 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (formula_2466 c3_depth c3_kind c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_133 c3_depth c3_kind c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_7574 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_6942 c3_kind)))

theorem normalization_7576 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (¬ (formula_2466 c3_depth c3_kind c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair097_133 c3_depth c3_kind c3_sign r3_group r3_level)) := (not_congr (normalization_7575 c3_depth c3_kind c3_sign r3_group r3_level))

theorem normalization_7577 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_2466 c3_depth c3_kind c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair097_133 c3_depth c3_kind c3_sign r3_group r3_level))) := (or_congr (normalization_4616 r3_mode) (or_congr (normalization_4618 r3_mode) (normalization_7576 c3_depth c3_kind c3_sign r3_group r3_level)))

theorem normalization_7578 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_2466 c3_depth c3_kind c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair097_133 c3_depth c3_kind c3_sign r3_group r3_level)))) := (not_congr (normalization_7577 c3_depth c3_kind c3_sign r3_group r3_level r3_mode))

theorem normalization_7579 (c3_node : Int) : ((c3_node % (2 : Int)) ≤ (0 : Int)) ↔ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7580 (c3_node : Int) : (¬ ((c3_node % (2 : Int)) ≤ (0 : Int))) ↔ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7579 c3_node))

theorem normalization_7581 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_7582 (c3_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_7581 c3_depth r3_level))

theorem normalization_7583 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7584 (c3_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_7583 c3_depth r3_level))

abbrev shared_expr_Repair097_134 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_7585 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (formula_2467 c3_depth c3_kind c3_node c3_sign r3_level) ↔ (shared_expr_Repair097_134 c3_depth c3_kind c3_node c3_sign r3_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7560 c3_sign) (or_congr (normalization_7580 c3_node) (or_congr (normalization_7582 c3_depth r3_level) (normalization_7584 c3_depth r3_level))))))

theorem normalization_7586 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (¬ (formula_2467 c3_depth c3_kind c3_node c3_sign r3_level)) ↔ (¬ (shared_expr_Repair097_134 c3_depth c3_kind c3_node c3_sign r3_level)) := (not_congr (normalization_7585 c3_depth c3_kind c3_node c3_sign r3_level))

abbrev shared_expr_Repair097_135 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair097_134 c3_depth c3_kind c3_node c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair097_130 c3_depth c3_kind c3_sign r3_level))))
theorem normalization_7587 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2468 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_135 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_7586 c3_depth c3_kind c3_node c3_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_7566 c3_depth c3_kind c3_sign r3_level)))

theorem normalization_7588 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (¬ (formula_2468 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair097_135 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (not_congr (normalization_7587 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

theorem normalization_7589 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_2468 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair097_135 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) := (or_congr (normalization_4626 r3_mode) (or_congr (normalization_4628 r3_mode) (normalization_7588 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))

theorem normalization_7590 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_2468 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair097_135 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) := (not_congr (normalization_7589 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

theorem normalization_7591 (c3_node : Int) : ((c3_node % (2 : Int)) ≥ (1 : Int)) ↔ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) := by
  omega

theorem normalization_7592 (c3_node : Int) : (¬ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := (not_congr (normalization_7591 c3_node))

abbrev shared_expr_Repair097_136 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_7593 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (formula_2469 c3_depth c3_kind c3_node c3_sign r3_level) ↔ (shared_expr_Repair097_136 c3_depth c3_kind c3_node c3_sign r3_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7560 c3_sign) (or_congr (normalization_7592 c3_node) (or_congr (normalization_7582 c3_depth r3_level) (normalization_7584 c3_depth r3_level))))))

theorem normalization_7594 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (¬ (formula_2469 c3_depth c3_kind c3_node c3_sign r3_level)) ↔ (¬ (shared_expr_Repair097_136 c3_depth c3_kind c3_node c3_sign r3_level)) := (not_congr (normalization_7593 c3_depth c3_kind c3_node c3_sign r3_level))

abbrev shared_expr_Repair097_137 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair097_136 c3_depth c3_kind c3_node c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair097_130 c3_depth c3_kind c3_sign r3_level))))
theorem normalization_7595 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2470 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_137 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_7594 c3_depth c3_kind c3_node c3_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_7566 c3_depth c3_kind c3_sign r3_level)))

theorem normalization_7596 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (¬ (formula_2470 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair097_137 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (not_congr (normalization_7595 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

theorem normalization_7597 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_2470 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair097_137 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) := (or_congr (normalization_4640 r3_mode) (or_congr (normalization_4642 r3_mode) (normalization_7596 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))

theorem normalization_7598 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_2470 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair097_137 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) := (not_congr (normalization_7597 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair097_138 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_7599 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (formula_2471 c3_depth c3_kind c3_node c3_sign r3_level) ↔ (shared_expr_Repair097_138 c3_depth c3_kind c3_node c3_sign r3_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7572 c3_sign) (or_congr (normalization_7580 c3_node) (or_congr (normalization_7582 c3_depth r3_level) (normalization_7584 c3_depth r3_level))))))

theorem normalization_7600 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (¬ (formula_2471 c3_depth c3_kind c3_node c3_sign r3_level)) ↔ (¬ (shared_expr_Repair097_138 c3_depth c3_kind c3_node c3_sign r3_level)) := (not_congr (normalization_7599 c3_depth c3_kind c3_node c3_sign r3_level))

abbrev shared_expr_Repair097_139 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair097_132 c3_depth c3_kind c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair097_138 c3_depth c3_kind c3_node c3_sign r3_level))))
theorem normalization_7601 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2472 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_139 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_7574 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_7600 c3_depth c3_kind c3_node c3_sign r3_level)))

theorem normalization_7602 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (¬ (formula_2472 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair097_139 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (not_congr (normalization_7601 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

theorem normalization_7603 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_2472 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair097_139 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) := (or_congr (normalization_4650 r3_mode) (or_congr (normalization_4651 r3_mode) (normalization_7602 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))

theorem normalization_7604 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_2472 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair097_139 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) := (not_congr (normalization_7603 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair097_140 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_7605 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (formula_2473 c3_depth c3_kind c3_node c3_sign r3_level) ↔ (shared_expr_Repair097_140 c3_depth c3_kind c3_node c3_sign r3_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7572 c3_sign) (or_congr (normalization_7592 c3_node) (or_congr (normalization_7582 c3_depth r3_level) (normalization_7584 c3_depth r3_level))))))

theorem normalization_7606 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (¬ (formula_2473 c3_depth c3_kind c3_node c3_sign r3_level)) ↔ (¬ (shared_expr_Repair097_140 c3_depth c3_kind c3_node c3_sign r3_level)) := (not_congr (normalization_7605 c3_depth c3_kind c3_node c3_sign r3_level))

abbrev shared_expr_Repair097_141 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair097_132 c3_depth c3_kind c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair097_140 c3_depth c3_kind c3_node c3_sign r3_level))))
theorem normalization_7607 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2474 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Repair097_141 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_7574 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_7606 c3_depth c3_kind c3_node c3_sign r3_level)))

theorem normalization_7608 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (¬ (formula_2474 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair097_141 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (not_congr (normalization_7607 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

theorem normalization_7609 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_2474 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair097_141 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) := (or_congr (normalization_4659 r3_mode) (or_congr (normalization_4661 r3_mode) (normalization_7608 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))

theorem normalization_7610 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_2474 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair097_141 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) := (not_congr (normalization_7609 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair097_142 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair097_131 c3_depth c3_kind c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair097_133 c3_depth c3_kind c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair097_135 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair097_137 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair097_139 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair097_141 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))))
theorem normalization_7611 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2475 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_142 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) := (or_congr (normalization_7570 c3_depth c3_kind c3_sign r3_group r3_level r3_mode) (or_congr (normalization_7578 c3_depth c3_kind c3_sign r3_group r3_level r3_mode) (or_congr (normalization_7590 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (or_congr (normalization_7598 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (or_congr (normalization_7604 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (normalization_7610 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))))))

theorem normalization_7612 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((formula_2532 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (formula_2475 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) ↔ ((shared_expr_Repair097_108 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_142 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) := (iff_congr (normalization_7455 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (normalization_7611 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair097_143 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair097_142 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
theorem normalization_7613 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2548 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_143 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_6903 c3_kind) (normalization_7544 c3_group c3_level c3_mode r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_6903 c3_kind)) (normalization_7611 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))

abbrev shared_expr_Repair097_144 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Repair097_109 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_143 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
theorem normalization_7614 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2549 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_144 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := (iff_congr (normalization_7456 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) (normalization_7613 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_6338 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2549 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_2154 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Repair097_108 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (shared_expr_Repair097_142 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))
  have n0 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6905 c3_kind) (replay_6106 c3_kind)
  have n1 : ((shared_expr_Repair097_1 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair097_127 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_7546 c3_group c3_level c3_mode r3_group r3_level r3_mode) (replay_6336 c3_group c3_level c3_mode r3_group r3_level r3_mode)
  have n2 : ((shared_expr_Repair097_108 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair097_142 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_7612 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (replay_6337 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_7614 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) hn

end H4Formal.Generated.Repair
