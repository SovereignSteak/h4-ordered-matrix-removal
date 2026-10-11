import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair112

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair113_0 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_2809 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_2809 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_2815 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair113_0 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_2394 (p0 p1 : Prop) : (((p0 ↔ p0)) → (p1 ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair113_1 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
abbrev shared_expr_Repair113_2 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_3 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_2 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Repair113_4 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_5 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_4 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Repair113_6 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair113_7 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_2 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_6 c3_depth c3_kind c3_node c3_sign r1_level)))
abbrev shared_expr_Repair113_8 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair113_9 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_2 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_8 c3_depth c3_kind c3_node c3_sign r1_level)))
abbrev shared_expr_Repair113_10 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair113_11 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_10 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_4 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Repair113_12 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair113_13 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_12 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_4 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Repair113_14 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_3 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_5 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair113_7 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair113_9 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair113_11 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair113_13 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
abbrev shared_expr_Repair113_15 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_1 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair113_14 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
abbrev shared_expr_Repair113_16 (c3_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_17 (c3_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_18 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_16 c3_level r1_depth r1_kind r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_17 c3_level r1_depth r1_kind r1_sign)))
abbrev shared_expr_Repair113_19 (c3_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_20 (c3_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_21 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_19 c3_level r1_depth r1_kind r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_20 c3_level r1_depth r1_kind r1_sign)))
abbrev shared_expr_Repair113_22 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair113_23 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_22 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_24 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair113_25 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_24 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_26 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair113_27 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_26 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_28 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair113_29 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_28 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair113_30 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_18 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((((c3_mode) ≤ (1 : Int)) ∧ (¬ ((c3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_21 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((((c3_mode) ≤ (2 : Int)) ∧ (¬ ((c3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair113_23 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (3 : Int)) ∧ (¬ ((c3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair113_25 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (4 : Int)) ∧ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair113_27 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (5 : Int)) ∧ (¬ ((c3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair113_29 c3_group c3_level r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Repair113_31 (c3_depth c3_kind h r1_kind : Int) : Prop := ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair113_32 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ∧ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair113_33 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair113_34 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Repair113_32 c3_node c3_sign h r1_depth r1_node r1_sign) ∨ (shared_expr_Repair113_33 c3_node c3_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Repair113_35 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
abbrev shared_expr_Repair113_36 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair113_37 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Repair113_35 c3_node c3_sign r1_node r1_sign) ∨ (shared_expr_Repair113_36 c3_node c3_sign r1_node r1_sign)))
abbrev shared_expr_Repair113_38 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair113_34 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (shared_expr_Repair113_37 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))
abbrev shared_expr_Repair113_39 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Repair113_38 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Repair113_40 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (¬ (shared_expr_Repair113_31 c3_depth c3_kind h r1_kind))) ∨ (shared_expr_Repair113_39 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign))
abbrev shared_expr_Repair113_41 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_30 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair113_40 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Repair113_42 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_15 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair113_41 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Repair113_43 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair113_42 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair113_42 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_7964 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2815 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair113_43 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_7955 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_7955 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair113_44 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Repair113_41 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair113_41 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign))
theorem replay_7617 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2815 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_2394 (shared_expr_Repair113_41 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) (shared_expr_Repair113_42 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : (shared_expr_Repair113_44 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := by
    exact Iff.mp (normalization_7963 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) (replay_7616 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_7964 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_7618 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i527 : ((formula_2789 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2809 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_7617 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_7614 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i527)

theorem normalized_2395 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of rewrite.
theorem replay_7619 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2815 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_2395 (shared_expr_Repair113_42 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_7964 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_7620 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i527 : ((formula_2789 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2809 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_7619 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_7618 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i527)

-- Checked replay of mp.
theorem replay_7621 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i527 : ((formula_2789 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2809 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_7617 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_7620 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i527)

-- Checked replay of mp.
theorem replay_7622 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i527 : ((formula_2789 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2809 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_7617 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_7621 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i527)

abbrev shared_expr_Repair113_45 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ (c3_kind = (2 : Int))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2816 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair113_45 c3_depth c3_kind c3_sign r1_group r1_level)

abbrev shared_expr_Repair113_46 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ (c3_kind = (2 : Int))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2817 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair113_46 c3_depth c3_kind c3_sign r1_group r1_level)

abbrev shared_expr_Repair113_47 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int)))))
abbrev formula_2818 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair113_47 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Repair113_48 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int)))))
abbrev formula_2819 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair113_48 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Repair113_49 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int)))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2820 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair113_49 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Repair113_50 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int)))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2821 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair113_50 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Repair113_51 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (0 : Int)) ∧ (formula_2816 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((r1_mode = (1 : Int)) ∧ (formula_2817 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((r1_mode = (2 : Int)) ∧ (formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((r1_mode = (3 : Int)) ∧ (formula_2819 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((r1_mode = (4 : Int)) ∧ (formula_2820 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((r1_mode = (5 : Int)) ∧ (formula_2821 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
abbrev formula_2822 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair113_51 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

abbrev shared_expr_Repair113_52 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((c3_kind = (0 : Int)) ∧ ((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group)))) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2822 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
abbrev formula_2823 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair113_52 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)

abbrev shared_expr_Repair113_53 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (((c3_group = (1 : Int)) ∧ ((r1_kind = (1 : Int)) ∧ (r1_depth = c3_level) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))))) ∨ ((¬ (c3_group = (1 : Int))) ∧ ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))))))
abbrev formula_2824 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair113_53 c3_group c3_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair113_54 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (((c3_group = (1 : Int)) ∧ ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))))) ∨ ((¬ (c3_group = (1 : Int))) ∧ ((r1_kind = (1 : Int)) ∧ (r1_depth = c3_level) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))))))
abbrev formula_2825 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair113_54 c3_group c3_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair113_55 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((c3_mode = (0 : Int)) ∧ (formula_2824 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((c3_mode = (1 : Int)) ∧ (formula_2825 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((c3_mode = (2 : Int)) ∧ (formula_2800 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c3_mode = (3 : Int)) ∧ (formula_2801 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c3_mode = (4 : Int)) ∧ (formula_2802 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c3_mode = (5 : Int)) ∧ (formula_2803 c3_group c3_level r1_depth r1_kind r1_node r1_sign)))
abbrev formula_2826 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair113_55 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair113_56 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ ((r1_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ ((r1_sign = (1 : Int)) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))
abbrev formula_2827 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair113_56 c3_node c3_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Repair113_57 (c3_node c3_sign r1_node r1_sign : Int) : Prop := ((((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c3_sign = (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ∨ (((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_2828 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Repair113_57 c3_node c3_sign r1_node r1_sign)

abbrev shared_expr_Repair113_58 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((r1_kind = (2 : Int)) ∨ (c3_kind = (2 : Int)))) ∧ (((r1_depth = c3_depth) ∧ (formula_2827 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (((r1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ (formula_2828 c3_node c3_sign r1_node r1_sign))))
abbrev shared_expr_Repair113_59 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind = (2 : Int)) ∨ (c3_kind = (2 : Int))) ∧ (¬ ((r1_kind = (2 : Int)) ∧ (c3_kind = (1 : Int)) ∧ (c3_depth = h)))) ∨ (shared_expr_Repair113_58 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign))
abbrev formula_2829 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair113_59 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair113_60 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((c3_kind = (0 : Int)) ∧ (formula_2826 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2829 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev formula_2830 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair113_60 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair113_61 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((r1_kind = (0 : Int)) ∧ (formula_2823 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) ∨ ((¬ (r1_kind = (0 : Int))) ∧ (formula_2830 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev formula_2831 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair113_61 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair113_62 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_2809 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_2831 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_2832 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair113_62 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

set_option maxHeartbeats 2000000 in
theorem normalized_2396 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15))) ∧ (¬ ((p47 ∧ (¬ p35)) ∧ (p15 ∧ (¬ p2)) ∧ (p52 ∧ (¬ p53))))) ∨ ((¬ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)))) ∧ ((((¬ p54) ∧ p55) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p56)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p56)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p59)))) ∨ (((¬ p60) ∧ p54) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p61) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p62)))))))))))) ↔ (((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15))) ∧ (¬ ((p47 ∧ (¬ p35)) ∧ (p15 ∧ (¬ p2)) ∧ (p52 ∧ (¬ p53))))) ∨ ((¬ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)))) ∧ ((((¬ p54) ∧ p55) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p56)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p56)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p59)))) ∨ (((¬ p60) ∧ p54) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p61) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p62))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7965 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

abbrev shared_expr_Repair113_63 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
theorem normalization_7966 (c3_depth c3_kind c3_sign r1_level : Int) : ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (shared_expr_Repair113_63 c3_depth c3_kind c3_sign r1_level) := (and_congr (normalization_6804 c3_kind) (and_congr (normalization_7965 c3_depth r1_level) (normalization_7102 c3_sign)))

abbrev shared_expr_Repair113_64 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_63 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_7967 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2816 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair113_64 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_6806 c3_kind)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_7966 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_7968 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (0 : Int)) ∧ (formula_2816 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_64 c3_depth c3_kind c3_sign r1_group r1_level)) := (and_congr (normalization_2771 r1_mode) (normalization_7967 c3_depth c3_kind c3_sign r1_group r1_level))

abbrev shared_expr_Repair113_65 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
theorem normalization_7969 (c3_depth c3_kind c3_sign r1_level : Int) : ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (shared_expr_Repair113_65 c3_depth c3_kind c3_sign r1_level) := (and_congr (normalization_6804 c3_kind) (and_congr (normalization_7965 c3_depth r1_level) (normalization_7106 c3_sign)))

abbrev shared_expr_Repair113_66 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_65 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_7970 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2817 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair113_66 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_6806 c3_kind)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_7969 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_7971 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (1 : Int)) ∧ (formula_2817 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_66 c3_depth c3_kind c3_sign r1_group r1_level)) := (and_congr (normalization_3230 r1_mode) (normalization_7970 c3_depth c3_kind c3_sign r1_group r1_level))

abbrev shared_expr_Repair113_67 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_63 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_6 c3_depth c3_kind c3_node c3_sign r1_level)))
theorem normalization_7972 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair113_67 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_7966 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_7907 c3_depth c3_kind c3_node c3_sign r1_level)))

theorem normalization_7973 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (2 : Int)) ∧ (formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair113_67 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_3234 r1_mode) (normalization_7972 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Repair113_68 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_63 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_8 c3_depth c3_kind c3_node c3_sign r1_level)))
theorem normalization_7974 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2819 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair113_68 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_7966 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_7910 c3_depth c3_kind c3_node c3_sign r1_level)))

theorem normalization_7975 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (3 : Int)) ∧ (formula_2819 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair113_68 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_3240 r1_mode) (normalization_7974 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Repair113_69 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_10 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_65 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_7976 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2820 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair113_69 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_7913 c3_depth c3_kind c3_node c3_sign r1_level)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_7969 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_7977 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (4 : Int)) ∧ (formula_2820 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair113_69 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_3244 r1_mode) (normalization_7976 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Repair113_70 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_12 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair113_65 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_7978 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2821 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair113_70 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_7916 c3_depth c3_kind c3_node c3_sign r1_level)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_7969 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_7979 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (5 : Int)) ∧ (formula_2821 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair113_70 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_3249 r1_mode) (normalization_7978 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Repair113_71 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_64 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_66 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair113_67 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair113_68 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair113_69 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair113_70 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
theorem normalization_7980 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2822 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair113_71 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := (or_congr (normalization_7968 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (or_congr (normalization_7971 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (or_congr (normalization_7973 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (or_congr (normalization_7975 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (or_congr (normalization_7977 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (normalization_7979 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))))))

abbrev shared_expr_Repair113_72 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_1 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair113_71 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
theorem normalization_7981 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2823 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair113_72 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_6792 c3_kind) (normalization_7899 c3_group c3_level c3_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_6792 c3_kind)) (normalization_7980 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))

theorem normalization_7982 (c3_level r1_depth : Int) : ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_7983 (c3_level r1_depth r1_kind r1_sign : Int) : ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int)))) ↔ (shared_expr_Repair113_17 c3_level r1_depth r1_kind r1_sign) := (and_congr (normalization_2282 r1_kind) (and_congr (normalization_7982 c3_level r1_depth) (normalization_3256 r1_sign)))

theorem normalization_7984 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : (formula_2824 c3_group c3_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Repair113_18 c3_group c3_level r1_depth r1_kind r1_sign) := (or_congr (and_congr (normalization_7130 c3_group) (normalization_7853 c3_level r1_depth r1_kind r1_sign)) (and_congr (not_congr (normalization_7130 c3_group)) (normalization_7983 c3_level r1_depth r1_kind r1_sign)))

theorem normalization_7985 (c3_group c3_level c3_mode r1_depth r1_kind r1_sign : Int) : ((c3_mode = (0 : Int)) ∧ (formula_2824 c3_group c3_level r1_depth r1_kind r1_sign)) ↔ ((((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_18 c3_group c3_level r1_depth r1_kind r1_sign)) := (and_congr (normalization_7129 c3_mode) (normalization_7984 c3_group c3_level r1_depth r1_kind r1_sign))

theorem normalization_7986 (c3_level r1_depth r1_kind r1_sign : Int) : ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int)))) ↔ (shared_expr_Repair113_19 c3_level r1_depth r1_kind r1_sign) := (and_congr (normalization_2282 r1_kind) (and_congr (normalization_7982 c3_level r1_depth) (normalization_3262 r1_sign)))

theorem normalization_7987 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : (formula_2825 c3_group c3_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Repair113_21 c3_group c3_level r1_depth r1_kind r1_sign) := (or_congr (and_congr (normalization_7130 c3_group) (normalization_7986 c3_level r1_depth r1_kind r1_sign)) (and_congr (not_congr (normalization_7130 c3_group)) (normalization_7859 c3_level r1_depth r1_kind r1_sign)))

theorem normalization_7988 (c3_group c3_level c3_mode r1_depth r1_kind r1_sign : Int) : ((c3_mode = (1 : Int)) ∧ (formula_2825 c3_group c3_level r1_depth r1_kind r1_sign)) ↔ ((((c3_mode) ≤ (1 : Int)) ∧ (¬ ((c3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair113_21 c3_group c3_level r1_depth r1_kind r1_sign)) := (and_congr (normalization_7137 c3_mode) (normalization_7987 c3_group c3_level r1_depth r1_kind r1_sign))

theorem normalization_7989 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : (formula_2826 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair113_30 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_7985 c3_group c3_level c3_mode r1_depth r1_kind r1_sign) (or_congr (normalization_7988 c3_group c3_level c3_mode r1_depth r1_kind r1_sign) (or_congr (normalization_7930 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) (or_congr (normalization_7933 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) (or_congr (normalization_7936 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) (normalization_7939 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign))))))

theorem normalization_7990 (c3_node r1_node : Int) : ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7991 (c3_node c3_sign r1_node r1_sign : Int) : ((r1_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_2287 r1_sign) (and_congr (normalization_7100 c3_sign) (normalization_7990 c3_node r1_node)))

theorem normalization_7992 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((r1_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (shared_expr_Repair113_32 c3_node c3_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_2779 r1_sign) (and_congr (normalization_7101 c3_sign) (and_congr (normalization_2778 h r1_depth) (normalization_7990 c3_node r1_node))))

theorem normalization_7993 (c3_node r1_node : Int) : ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) ↔ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7994 (c3_node r1_node : Int) : (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := (not_congr (normalization_7993 c3_node r1_node))

theorem normalization_7995 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((r1_sign = (1 : Int)) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair113_33 c3_node c3_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_2479 r1_sign) (and_congr (normalization_6809 c3_sign) (and_congr (normalization_2850 h r1_depth) (normalization_7994 c3_node r1_node))))

theorem normalization_7996 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2827 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Repair113_34 c3_node c3_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_7991 c3_node c3_sign r1_node r1_sign) (or_congr (normalization_7992 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_7995 c3_node c3_sign h r1_depth r1_node r1_sign)))

theorem normalization_7997 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((r1_depth = c3_depth) ∧ (formula_2827 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair113_34 c3_node c3_sign h r1_depth r1_node r1_sign)) := (and_congr (normalization_7878 c3_depth r1_depth) (normalization_7996 c3_node c3_sign h r1_depth r1_node r1_sign))

theorem normalization_7998 (c3_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7999 (c3_node r1_node : Int) : ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_8000 (c3_node c3_sign r1_node r1_sign : Int) : (((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c3_sign = (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (shared_expr_Repair113_35 c3_node c3_sign r1_node r1_sign) := (and_congr (normalization_3256 r1_sign) (and_congr (normalization_7100 c3_sign) (normalization_7999 c3_node r1_node)))

theorem normalization_8001 (c3_node r1_node : Int) : ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8002 (c3_node r1_node : Int) : (¬ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_8001 c3_node r1_node))

theorem normalization_8003 (c3_node c3_sign r1_node r1_sign : Int) : (((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))) ↔ (shared_expr_Repair113_36 c3_node c3_sign r1_node r1_sign) := (and_congr (normalization_3262 r1_sign) (and_congr (normalization_6809 c3_sign) (normalization_8002 c3_node r1_node)))

theorem normalization_8004 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2828 c3_node c3_sign r1_node r1_sign) ↔ ((shared_expr_Repair113_35 c3_node c3_sign r1_node r1_sign) ∨ (shared_expr_Repair113_36 c3_node c3_sign r1_node r1_sign)) := (or_congr (normalization_8000 c3_node c3_sign r1_node r1_sign) (normalization_8003 c3_node c3_sign r1_node r1_sign))

theorem normalization_8005 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : (((r1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ (formula_2828 c3_node c3_sign r1_node r1_sign)) ↔ (shared_expr_Repair113_37 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) := (and_congr (normalization_7998 c3_depth r1_depth) (normalization_8004 c3_node c3_sign r1_node r1_sign))

theorem normalization_8006 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (((r1_depth = c3_depth) ∧ (formula_2827 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (((r1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ (formula_2828 c3_node c3_sign r1_node r1_sign))) ↔ (shared_expr_Repair113_38 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_7997 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_8005 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))

theorem normalization_8007 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2829 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair113_40 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_7875 c3_kind r1_kind) (normalization_7877 c3_depth c3_kind h r1_kind)) (and_congr (not_congr (normalization_7875 c3_kind r1_kind)) (normalization_8006 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)))

theorem normalization_8008 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2830 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair113_41 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_6792 c3_kind) (normalization_7989 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) (and_congr (not_congr (normalization_6792 c3_kind)) (normalization_8007 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair113_73 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair113_72 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair113_41 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_8009 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2831 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair113_73 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (and_congr (normalization_2270 r1_kind) (normalization_7981 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_2270 r1_kind)) (normalization_8008 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair113_74 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair113_42 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair113_73 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_8010 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2832 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair113_74 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_7955 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_8009 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_7623 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2832 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_2396 ((r1_kind) ≤ (0 : Int)) ((r1_kind) ≤ (-1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ((r1_mode) ≤ (0 : Int)) ((r1_mode) ≤ (-1 : Int)) ((r1_group) ≤ (1 : Int)) ((r1_group) ≤ (0 : Int)) ((c3_kind) ≤ (2 : Int)) ((c3_kind) ≤ (1 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (2 : Int)) ((c3_sign) ≤ (1 : Int)) ((r1_mode) ≤ (1 : Int)) ((r1_mode) ≤ (2 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((r1_mode) ≤ (3 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int)) ((r1_mode) ≤ (4 : Int)) ((r1_mode) ≤ (5 : Int)) ((c3_mode) ≤ (0 : Int)) ((c3_mode) ≤ (-1 : Int)) ((c3_group) ≤ (1 : Int)) ((c3_group) ≤ (0 : Int)) ((r1_kind) ≤ (1 : Int)) ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)) ((r1_sign) ≤ (2 : Int)) ((r1_sign) ≤ (1 : Int)) ((c3_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ((c3_mode) ≤ (1 : Int)) ((c3_mode) ≤ (2 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((r1_kind) ≤ (2 : Int)) ((c3_mode) ≤ (3 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int)) ((c3_mode) ≤ (4 : Int)) ((c3_mode) ≤ (5 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8010 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_7624 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i527 : ((formula_2789 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2831 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_7623 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_7622 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i527)

theorem normalized_2397 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8011 (c3_mode r1_mode : Int) : (r1_mode ≤ c3_mode) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8012 (c3_mode r1_mode : Int) : (r1_mode ≥ c3_mode) ↔ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_8013 (c3_mode r1_mode : Int) : ((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (and_congr (normalization_8011 c3_mode r1_mode) (normalization_8012 c3_mode r1_mode))

abbrev shared_expr_Repair113_75 (c3_mode r1_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
theorem normalization_8014 (c3_mode r1_mode : Int) : ((r1_mode = c3_mode) ↔ ((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode))) ↔ (shared_expr_Repair113_75 c3_mode r1_mode) := (iff_congr (normalization_7824 c3_mode r1_mode) (normalization_8013 c3_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_7625 (c3_mode r1_mode : Int) : ((r1_mode = c3_mode) ↔ ((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode))) := by
  classical
  have ht := (normalized_2397 ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8014 c3_mode r1_mode) hn

theorem normalized_2398 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8015 (c3_mode r1_mode : Int) : ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8016 (c3_mode r1_mode : Int) : ((r1_mode ≤ c3_mode) ↔ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_8011 c3_mode r1_mode) (normalization_8015 c3_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_7626 (c3_mode r1_mode : Int) : ((r1_mode ≤ c3_mode) ↔ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2398 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8016 c3_mode r1_mode) hn

theorem normalized_2399 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8017 (c3_mode r1_mode : Int) : ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_8018 (c3_mode r1_mode : Int) : ((r1_mode ≥ c3_mode) ↔ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (iff_congr (normalization_8012 c3_mode r1_mode) (normalization_8017 c3_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_7627 (c3_mode r1_mode : Int) : ((r1_mode ≥ c3_mode) ↔ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2399 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8018 c3_mode r1_mode) hn

theorem normalized_2400 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8019 (c3_mode r1_mode : Int) : (((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (and_congr (normalization_8015 c3_mode r1_mode) (normalization_8017 c3_mode r1_mode))

theorem normalization_8020 (c3_mode r1_mode : Int) : (((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ (((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Repair113_75 c3_mode r1_mode) := (iff_congr (normalization_8013 c3_mode r1_mode) (normalization_8019 c3_mode r1_mode))

-- Checked replay of monotonicity.
theorem replay_7628 (c3_mode r1_mode : Int) : (((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ (((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2400 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8016 c3_mode r1_mode) (replay_7626 c3_mode r1_mode)
  have n1 : (((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8018 c3_mode r1_mode) (replay_7627 c3_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8020 c3_mode r1_mode) hn

abbrev shared_expr_Repair113_76 (c3_mode r1_mode : Int) : Prop := ((((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))))
abbrev formula_2833 (c3_mode r1_mode : Int) : Prop := (shared_expr_Repair113_76 c3_mode r1_mode)

theorem normalized_2401 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8021 (c3_mode r1_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_8015 c3_mode r1_mode))

theorem normalization_8022 (c3_mode r1_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (not_congr (normalization_8017 c3_mode r1_mode))

theorem normalization_8023 (c3_mode r1_mode : Int) : ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))) := (or_congr (normalization_8021 c3_mode r1_mode) (normalization_8022 c3_mode r1_mode))

theorem normalization_8024 (c3_mode r1_mode : Int) : (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) := (not_congr (normalization_8023 c3_mode r1_mode))

abbrev shared_expr_Repair113_77 (c3_mode r1_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))))
theorem normalization_8025 (c3_mode r1_mode : Int) : (formula_2833 c3_mode r1_mode) ↔ (shared_expr_Repair113_77 c3_mode r1_mode) := (iff_congr (normalization_8019 c3_mode r1_mode) (normalization_8024 c3_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_7629 (c3_mode r1_mode : Int) : (formula_2833 c3_mode r1_mode) := by
  classical
  have ht := (normalized_2401 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8025 c3_mode r1_mode) hn

theorem normalized_2402 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8026 (c3_mode r1_mode : Int) : (((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair113_77 c3_mode r1_mode) := (iff_congr (normalization_8013 c3_mode r1_mode) (normalization_8024 c3_mode r1_mode))

-- Checked replay of trans.
theorem replay_7630 (c3_mode r1_mode : Int) : (((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2402 ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) (shared_expr_Repair113_77 c3_mode r1_mode))
  have n0 : (shared_expr_Repair113_75 c3_mode r1_mode) := by
    exact Iff.mp (normalization_8020 c3_mode r1_mode) (replay_7628 c3_mode r1_mode)
  have n1 : (shared_expr_Repair113_77 c3_mode r1_mode) := by
    exact Iff.mp (normalization_8025 c3_mode r1_mode) (replay_7629 c3_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8026 c3_mode r1_mode) hn

theorem normalized_2403 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8027 (c3_mode r1_mode : Int) : ((r1_mode = c3_mode) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair113_77 c3_mode r1_mode) := (iff_congr (normalization_7824 c3_mode r1_mode) (normalization_8024 c3_mode r1_mode))

-- Checked replay of trans.
theorem replay_7631 (c3_mode r1_mode : Int) : ((r1_mode = c3_mode) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2403 ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) (shared_expr_Repair113_77 c3_mode r1_mode))
  have n0 : (shared_expr_Repair113_75 c3_mode r1_mode) := by
    exact Iff.mp (normalization_8014 c3_mode r1_mode) (replay_7625 c3_mode r1_mode)
  have n1 : (shared_expr_Repair113_77 c3_mode r1_mode) := by
    exact Iff.mp (normalization_8026 c3_mode r1_mode) (replay_7630 c3_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8027 c3_mode r1_mode) hn

theorem normalized_2404 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8028 (c3_level r1_level : Int) : (r1_level ≤ c3_level) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8029 (c3_level r1_level : Int) : (r1_level ≥ c3_level) ↔ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_8030 (c3_level r1_level : Int) : ((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (and_congr (normalization_8028 c3_level r1_level) (normalization_8029 c3_level r1_level))

abbrev shared_expr_Repair113_78 (c3_level r1_level : Int) : Prop := (((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
theorem normalization_8031 (c3_level r1_level : Int) : ((r1_level = c3_level) ↔ ((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level))) ↔ (shared_expr_Repair113_78 c3_level r1_level) := (iff_congr (normalization_7825 c3_level r1_level) (normalization_8030 c3_level r1_level))

-- Checked replay of rewrite.
theorem replay_7632 (c3_level r1_level : Int) : ((r1_level = c3_level) ↔ ((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level))) := by
  classical
  have ht := (normalized_2404 ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8031 c3_level r1_level) hn

theorem normalized_2405 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8032 (c3_level r1_level : Int) : ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8033 (c3_level r1_level : Int) : ((r1_level ≤ c3_level) ↔ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_8028 c3_level r1_level) (normalization_8032 c3_level r1_level))

-- Checked replay of rewrite.
theorem replay_7633 (c3_level r1_level : Int) : ((r1_level ≤ c3_level) ↔ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2405 ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8033 c3_level r1_level) hn

theorem normalized_2406 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8034 (c3_level r1_level : Int) : ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_8035 (c3_level r1_level : Int) : ((r1_level ≥ c3_level) ↔ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (iff_congr (normalization_8029 c3_level r1_level) (normalization_8034 c3_level r1_level))

-- Checked replay of rewrite.
theorem replay_7634 (c3_level r1_level : Int) : ((r1_level ≥ c3_level) ↔ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2406 ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8035 c3_level r1_level) hn

theorem normalized_2407 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8036 (c3_level r1_level : Int) : (((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (and_congr (normalization_8032 c3_level r1_level) (normalization_8034 c3_level r1_level))

theorem normalization_8037 (c3_level r1_level : Int) : (((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ (((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ (shared_expr_Repair113_78 c3_level r1_level) := (iff_congr (normalization_8030 c3_level r1_level) (normalization_8036 c3_level r1_level))

-- Checked replay of monotonicity.
theorem replay_7635 (c3_level r1_level : Int) : (((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ (((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2407 ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8033 c3_level r1_level) (replay_7633 c3_level r1_level)
  have n1 : (((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8035 c3_level r1_level) (replay_7634 c3_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8037 c3_level r1_level) hn

abbrev shared_expr_Repair113_79 (c3_level r1_level : Int) : Prop := ((((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))))
abbrev formula_2834 (c3_level r1_level : Int) : Prop := (shared_expr_Repair113_79 c3_level r1_level)

theorem normalized_2408 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8038 (c3_level r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_8032 c3_level r1_level))

theorem normalization_8039 (c3_level r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_8034 c3_level r1_level))

theorem normalization_8040 (c3_level r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) := (or_congr (normalization_8038 c3_level r1_level) (normalization_8039 c3_level r1_level))

theorem normalization_8041 (c3_level r1_level : Int) : (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) := (not_congr (normalization_8040 c3_level r1_level))

abbrev shared_expr_Repair113_80 (c3_level r1_level : Int) : Prop := (((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))))
theorem normalization_8042 (c3_level r1_level : Int) : (formula_2834 c3_level r1_level) ↔ (shared_expr_Repair113_80 c3_level r1_level) := (iff_congr (normalization_8036 c3_level r1_level) (normalization_8041 c3_level r1_level))

-- Checked replay of rewrite.
theorem replay_7636 (c3_level r1_level : Int) : (formula_2834 c3_level r1_level) := by
  classical
  have ht := (normalized_2408 ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8042 c3_level r1_level) hn

theorem normalized_2409 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8043 (c3_level r1_level : Int) : (((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair113_80 c3_level r1_level) := (iff_congr (normalization_8030 c3_level r1_level) (normalization_8041 c3_level r1_level))

-- Checked replay of trans.
theorem replay_7637 (c3_level r1_level : Int) : (((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2409 ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) (shared_expr_Repair113_80 c3_level r1_level))
  have n0 : (shared_expr_Repair113_78 c3_level r1_level) := by
    exact Iff.mp (normalization_8037 c3_level r1_level) (replay_7635 c3_level r1_level)
  have n1 : (shared_expr_Repair113_80 c3_level r1_level) := by
    exact Iff.mp (normalization_8042 c3_level r1_level) (replay_7636 c3_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8043 c3_level r1_level) hn

theorem normalized_2410 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8044 (c3_level r1_level : Int) : ((r1_level = c3_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair113_80 c3_level r1_level) := (iff_congr (normalization_7825 c3_level r1_level) (normalization_8041 c3_level r1_level))

-- Checked replay of trans.
theorem replay_7638 (c3_level r1_level : Int) : ((r1_level = c3_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2410 ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) (shared_expr_Repair113_80 c3_level r1_level))
  have n0 : (shared_expr_Repair113_78 c3_level r1_level) := by
    exact Iff.mp (normalization_8031 c3_level r1_level) (replay_7632 c3_level r1_level)
  have n1 : (shared_expr_Repair113_80 c3_level r1_level) := by
    exact Iff.mp (normalization_8043 c3_level r1_level) (replay_7637 c3_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8044 c3_level r1_level) hn

theorem normalized_2411 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8045 (c3_group r1_group : Int) : (r1_group ≤ c3_group) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8046 (c3_group r1_group : Int) : (r1_group ≥ c3_group) ↔ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_8047 (c3_group r1_group : Int) : ((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (and_congr (normalization_8045 c3_group r1_group) (normalization_8046 c3_group r1_group))

abbrev shared_expr_Repair113_81 (c3_group r1_group : Int) : Prop := (((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
theorem normalization_8048 (c3_group r1_group : Int) : ((r1_group = c3_group) ↔ ((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group))) ↔ (shared_expr_Repair113_81 c3_group r1_group) := (iff_congr (normalization_7897 c3_group r1_group) (normalization_8047 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_7639 (c3_group r1_group : Int) : ((r1_group = c3_group) ↔ ((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group))) := by
  classical
  have ht := (normalized_2411 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8048 c3_group r1_group) hn

theorem normalized_2412 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8049 (c3_group r1_group : Int) : ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8050 (c3_group r1_group : Int) : ((r1_group ≤ c3_group) ↔ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_8045 c3_group r1_group) (normalization_8049 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_7640 (c3_group r1_group : Int) : ((r1_group ≤ c3_group) ↔ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2412 ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8050 c3_group r1_group) hn

theorem normalized_2413 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8051 (c3_group r1_group : Int) : ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_8052 (c3_group r1_group : Int) : ((r1_group ≥ c3_group) ↔ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (iff_congr (normalization_8046 c3_group r1_group) (normalization_8051 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_7641 (c3_group r1_group : Int) : ((r1_group ≥ c3_group) ↔ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2413 ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8052 c3_group r1_group) hn

theorem normalized_2414 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8053 (c3_group r1_group : Int) : (((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (and_congr (normalization_8049 c3_group r1_group) (normalization_8051 c3_group r1_group))

theorem normalization_8054 (c3_group r1_group : Int) : (((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ (((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ↔ (shared_expr_Repair113_81 c3_group r1_group) := (iff_congr (normalization_8047 c3_group r1_group) (normalization_8053 c3_group r1_group))

-- Checked replay of monotonicity.
theorem replay_7642 (c3_group r1_group : Int) : (((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ (((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2414 ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8050 c3_group r1_group) (replay_7640 c3_group r1_group)
  have n1 : (((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8052 c3_group r1_group) (replay_7641 c3_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8054 c3_group r1_group) hn

abbrev shared_expr_Repair113_82 (c3_group r1_group : Int) : Prop := ((((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))
abbrev formula_2835 (c3_group r1_group : Int) : Prop := (shared_expr_Repair113_82 c3_group r1_group)

theorem normalized_2415 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8055 (c3_group r1_group : Int) : (¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_8049 c3_group r1_group))

theorem normalization_8056 (c3_group r1_group : Int) : (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (not_congr (normalization_8051 c3_group r1_group))

theorem normalization_8057 (c3_group r1_group : Int) : ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) := (or_congr (normalization_8055 c3_group r1_group) (normalization_8056 c3_group r1_group))

theorem normalization_8058 (c3_group r1_group : Int) : (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))) := (not_congr (normalization_8057 c3_group r1_group))

abbrev shared_expr_Repair113_83 (c3_group r1_group : Int) : Prop := (((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_8059 (c3_group r1_group : Int) : (formula_2835 c3_group r1_group) ↔ (shared_expr_Repair113_83 c3_group r1_group) := (iff_congr (normalization_8053 c3_group r1_group) (normalization_8058 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_7643 (c3_group r1_group : Int) : (formula_2835 c3_group r1_group) := by
  classical
  have ht := (normalized_2415 ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8059 c3_group r1_group) hn

theorem normalized_2416 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8060 (c3_group r1_group : Int) : (((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair113_83 c3_group r1_group) := (iff_congr (normalization_8047 c3_group r1_group) (normalization_8058 c3_group r1_group))

-- Checked replay of trans.
theorem replay_7644 (c3_group r1_group : Int) : (((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2416 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) (shared_expr_Repair113_83 c3_group r1_group))
  have n0 : (shared_expr_Repair113_81 c3_group r1_group) := by
    exact Iff.mp (normalization_8054 c3_group r1_group) (replay_7642 c3_group r1_group)
  have n1 : (shared_expr_Repair113_83 c3_group r1_group) := by
    exact Iff.mp (normalization_8059 c3_group r1_group) (replay_7643 c3_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8060 c3_group r1_group) hn

theorem normalized_2417 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8061 (c3_group r1_group : Int) : ((r1_group = c3_group) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair113_83 c3_group r1_group) := (iff_congr (normalization_7897 c3_group r1_group) (normalization_8058 c3_group r1_group))

-- Checked replay of trans.
theorem replay_7645 (c3_group r1_group : Int) : ((r1_group = c3_group) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2417 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) (shared_expr_Repair113_83 c3_group r1_group))
  have n0 : (shared_expr_Repair113_81 c3_group r1_group) := by
    exact Iff.mp (normalization_8048 c3_group r1_group) (replay_7639 c3_group r1_group)
  have n1 : (shared_expr_Repair113_83 c3_group r1_group) := by
    exact Iff.mp (normalization_8060 c3_group r1_group) (replay_7644 c3_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8061 c3_group r1_group) hn

theorem normalized_2418 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8062 (c3_group r1_group : Int) : (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))) := (not_congr (normalization_8058 c3_group r1_group))

abbrev shared_expr_Repair113_84 (c3_group r1_group : Int) : Prop := ((¬ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))))
theorem normalization_8063 (c3_group r1_group : Int) : ((¬ (r1_group = c3_group)) ↔ (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Repair113_84 c3_group r1_group) := (iff_congr (normalization_7898 c3_group r1_group) (normalization_8062 c3_group r1_group))

-- Checked replay of monotonicity.
theorem replay_7646 (c3_group r1_group : Int) : ((¬ (r1_group = c3_group)) ↔ (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_2418 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair113_83 c3_group r1_group) := by
    exact Iff.mp (normalization_8061 c3_group r1_group) (replay_7645 c3_group r1_group)
  have hn := ht n0
  exact Iff.mpr (normalization_8063 c3_group r1_group) hn

abbrev shared_expr_Repair113_85 (c3_group r1_group : Int) : Prop := ((¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2836 (c3_group r1_group : Int) : Prop := (shared_expr_Repair113_85 c3_group r1_group)

theorem normalized_2419 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair113_86 (c3_group r1_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_8064 (c3_group r1_group : Int) : (formula_2836 c3_group r1_group) ↔ (shared_expr_Repair113_86 c3_group r1_group) := (iff_congr (normalization_8062 c3_group r1_group) (normalization_8057 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_7647 (c3_group r1_group : Int) : (formula_2836 c3_group r1_group) := by
  classical
  have ht := (normalized_2419 ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8064 c3_group r1_group) hn

theorem normalized_2420 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair113_87 (c3_group r1_group : Int) : Prop := ((¬ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_8065 (c3_group r1_group : Int) : ((¬ (r1_group = c3_group)) ↔ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) ↔ (shared_expr_Repair113_87 c3_group r1_group) := (iff_congr (normalization_7898 c3_group r1_group) (normalization_8057 c3_group r1_group))

-- Checked replay of trans.
theorem replay_7648 (c3_group r1_group : Int) : ((¬ (r1_group = c3_group)) ↔ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_2420 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair113_84 c3_group r1_group) := by
    exact Iff.mp (normalization_8063 c3_group r1_group) (replay_7646 c3_group r1_group)
  have n1 : (shared_expr_Repair113_86 c3_group r1_group) := by
    exact Iff.mp (normalization_8064 c3_group r1_group) (replay_7647 c3_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8065 c3_group r1_group) hn

abbrev shared_expr_Repair113_88 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ∧ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2837 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair113_88 c3_group c3_level c3_mode r1_group r1_level r1_mode)

theorem normalized_2421 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair113_89 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_8066 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (formula_2837 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair113_89 c3_group c3_level c3_mode r1_group r1_level r1_mode) := (and_congr (normalization_8024 c3_mode r1_mode) (and_congr (normalization_8041 c3_level r1_level) (normalization_8057 c3_group r1_group)))

theorem normalization_8067 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group))) ↔ (formula_2837 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ↔ ((shared_expr_Repair113_1 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair113_89 c3_group c3_level c3_mode r1_group r1_level r1_mode)) := (iff_congr (normalization_7899 c3_group c3_level c3_mode r1_group r1_level r1_mode) (normalization_8066 c3_group c3_level c3_mode r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_7649 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group))) ↔ (formula_2837 c3_group c3_level c3_mode r1_group r1_level r1_mode)) := by
  classical
  have ht := (normalized_2421 ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))) ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair113_77 c3_mode r1_mode) := by
    exact Iff.mp (normalization_8027 c3_mode r1_mode) (replay_7631 c3_mode r1_mode)
  have n1 : (shared_expr_Repair113_80 c3_level r1_level) := by
    exact Iff.mp (normalization_8044 c3_level r1_level) (replay_7638 c3_level r1_level)
  have n2 : (shared_expr_Repair113_87 c3_group r1_group) := by
    exact Iff.mp (normalization_8065 c3_group r1_group) (replay_7648 c3_group r1_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8067 c3_group c3_level c3_mode r1_group r1_level r1_mode) hn

theorem normalized_2422 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair113_90 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_8068 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (formula_2706 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair113_90 c3_group c3_level c3_mode r1_group r1_level r1_mode) := (or_congr (normalization_8021 c3_mode r1_mode) (or_congr (normalization_8022 c3_mode r1_mode) (or_congr (normalization_8038 c3_level r1_level) (or_congr (normalization_8039 c3_level r1_level) (normalization_8058 c3_group r1_group)))))

theorem normalization_8069 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (¬ (formula_2706 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ↔ (¬ (shared_expr_Repair113_90 c3_group c3_level c3_mode r1_group r1_level r1_mode)) := (not_congr (normalization_8068 c3_group c3_level c3_mode r1_group r1_level r1_mode))

theorem normalization_8070 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : ((formula_2837 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (formula_2706 c3_group c3_level c3_mode r1_group r1_level r1_mode))) ↔ ((shared_expr_Repair113_89 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Repair113_90 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := (iff_congr (normalization_8066 c3_group c3_level c3_mode r1_group r1_level r1_mode) (normalization_8069 c3_group c3_level c3_mode r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_7650 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : ((formula_2837 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (formula_2706 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := by
  classical
  have ht := (normalized_2422 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8070 c3_group c3_level c3_mode r1_group r1_level r1_mode) hn

theorem normalized_2423 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8071 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group))) ↔ (¬ (formula_2706 c3_group c3_level c3_mode r1_group r1_level r1_mode))) ↔ ((shared_expr_Repair113_1 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Repair113_90 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := (iff_congr (normalization_7899 c3_group c3_level c3_mode r1_group r1_level r1_mode) (normalization_8069 c3_group c3_level c3_mode r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_7651 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group))) ↔ (¬ (formula_2706 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := by
  classical
  have ht := (normalized_2423 (shared_expr_Repair113_1 c3_group c3_level c3_mode r1_group r1_level r1_mode) (shared_expr_Repair113_89 c3_group c3_level c3_mode r1_group r1_level r1_mode) (shared_expr_Repair113_90 c3_group c3_level c3_mode r1_group r1_level r1_mode))
  have n0 : ((shared_expr_Repair113_1 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair113_89 c3_group c3_level c3_mode r1_group r1_level r1_mode)) := by
    exact Iff.mp (normalization_8067 c3_group c3_level c3_mode r1_group r1_level r1_mode) (replay_7649 c3_group c3_level c3_mode r1_group r1_level r1_mode)
  have n1 : ((shared_expr_Repair113_89 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Repair113_90 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := by
    exact Iff.mp (normalization_8070 c3_group c3_level c3_mode r1_group r1_level r1_mode) (replay_7650 c3_group c3_level c3_mode r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8071 c3_group c3_level c3_mode r1_group r1_level r1_mode) hn

theorem normalized_2424 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8072 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_8073 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_8074 (c3_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := (and_congr (normalization_8072 c3_depth r1_level) (normalization_8073 c3_depth r1_level))

abbrev shared_expr_Repair113_91 (c3_depth r1_level : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_8075 (c3_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Repair113_91 c3_depth r1_level) := (iff_congr (normalization_7965 c3_depth r1_level) (normalization_8074 c3_depth r1_level))

-- Checked replay of rewrite.
theorem replay_7652 (c3_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2424 ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8075 c3_depth r1_level) hn

abbrev shared_expr_Repair113_92 (c3_depth r1_level : Int) : Prop := ((((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))
abbrev formula_2838 (c3_depth r1_level : Int) : Prop := (shared_expr_Repair113_92 c3_depth r1_level)

theorem normalized_2425 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8076 (c3_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) := (not_congr (normalization_8072 c3_depth r1_level))

theorem normalization_8077 (c3_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := (not_congr (normalization_8073 c3_depth r1_level))

theorem normalization_8078 (c3_depth r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (or_congr (normalization_8076 c3_depth r1_level) (normalization_8077 c3_depth r1_level))

theorem normalization_8079 (c3_depth r1_level : Int) : (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) := (not_congr (normalization_8078 c3_depth r1_level))

abbrev shared_expr_Repair113_93 (c3_depth r1_level : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))))
theorem normalization_8080 (c3_depth r1_level : Int) : (formula_2838 c3_depth r1_level) ↔ (shared_expr_Repair113_93 c3_depth r1_level) := (iff_congr (normalization_8074 c3_depth r1_level) (normalization_8079 c3_depth r1_level))

-- Checked replay of rewrite.
theorem replay_7653 (c3_depth r1_level : Int) : (formula_2838 c3_depth r1_level) := by
  classical
  have ht := (normalized_2425 ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8080 c3_depth r1_level) hn

theorem normalized_2426 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8081 (c3_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Repair113_93 c3_depth r1_level) := (iff_congr (normalization_7965 c3_depth r1_level) (normalization_8079 c3_depth r1_level))

-- Checked replay of trans.
theorem replay_7654 (c3_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2426 ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) (shared_expr_Repair113_93 c3_depth r1_level))
  have n0 : (shared_expr_Repair113_91 c3_depth r1_level) := by
    exact Iff.mp (normalization_8075 c3_depth r1_level) (replay_7652 c3_depth r1_level)
  have n1 : (shared_expr_Repair113_93 c3_depth r1_level) := by
    exact Iff.mp (normalization_8080 c3_depth r1_level) (replay_7653 c3_depth r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8081 c3_depth r1_level) hn

theorem normalized_2427 (p0 p1 p2 p3 : Prop) : (((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair113_94 (c3_sign : Int) : Prop := (((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
theorem normalization_8082 (c3_sign : Int) : (((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ↔ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ↔ (shared_expr_Repair113_94 c3_sign) := (iff_congr (normalization_7102 c3_sign) (normalization_7559 c3_sign))

-- Checked replay of rewrite.
theorem replay_7655 (c3_sign : Int) : (((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ↔ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_2427 ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (2 : Int)) ((c3_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8082 c3_sign) hn

abbrev shared_expr_Repair113_95 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ∧ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))))
abbrev formula_2839 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := (shared_expr_Repair113_95 c3_depth c3_kind c3_sign r1_level)

theorem normalized_2428 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → ((p0 ∧ p2 ∧ p4) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair113_96 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
theorem normalization_8083 (c3_depth c3_kind c3_sign r1_level : Int) : (formula_2839 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Repair113_96 c3_depth c3_kind c3_sign r1_level) := (and_congr (normalization_6932 c3_kind) (and_congr (normalization_8079 c3_depth r1_level) (normalization_7559 c3_sign)))

theorem normalization_8084 (c3_depth c3_kind c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (formula_2839 c3_depth c3_kind c3_sign r1_level)) ↔ ((shared_expr_Repair113_63 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Repair113_96 c3_depth c3_kind c3_sign r1_level)) := (iff_congr (normalization_7966 c3_depth c3_kind c3_sign r1_level) (normalization_8083 c3_depth c3_kind c3_sign r1_level))

-- Checked replay of monotonicity.
theorem replay_7656 (c3_depth c3_kind c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (formula_2839 c3_depth c3_kind c3_sign r1_level)) := by
  classical
  have ht := (normalized_2428 (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
  have n0 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6934 c3_kind) (replay_6116 c3_kind)
  have n1 : (shared_expr_Repair113_93 c3_depth r1_level) := by
    exact Iff.mp (normalization_8081 c3_depth r1_level) (replay_7654 c3_depth r1_level)
  have n2 : (shared_expr_Repair113_94 c3_sign) := by
    exact Iff.mp (normalization_8082 c3_sign) (replay_7655 c3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8084 c3_depth c3_kind c3_sign r1_level) hn

theorem normalized_2429 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ (¬ p2)) ∨ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair113_97 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_8085 (c3_depth c3_kind c3_sign r1_level : Int) : (formula_2590 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Repair113_97 c3_depth c3_kind c3_sign r1_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7560 c3_sign) (or_congr (normalization_8076 c3_depth r1_level) (normalization_8077 c3_depth r1_level)))))

theorem normalization_8086 (c3_depth c3_kind c3_sign r1_level : Int) : (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level)) ↔ (¬ (shared_expr_Repair113_97 c3_depth c3_kind c3_sign r1_level)) := (not_congr (normalization_8085 c3_depth c3_kind c3_sign r1_level))

theorem normalization_8087 (c3_depth c3_kind c3_sign r1_level : Int) : ((formula_2839 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))) ↔ ((shared_expr_Repair113_96 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair113_97 c3_depth c3_kind c3_sign r1_level))) := (iff_congr (normalization_8083 c3_depth c3_kind c3_sign r1_level) (normalization_8086 c3_depth c3_kind c3_sign r1_level))

-- Checked replay of rewrite.
theorem replay_7657 (c3_depth c3_kind c3_sign r1_level : Int) : ((formula_2839 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))) := by
  classical
  have ht := (normalized_2429 ((c3_kind) ≤ (1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
  have hn := ht
  exact Iff.mpr (normalization_8087 c3_depth c3_kind c3_sign r1_level) hn

theorem normalized_2430 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8088 (c3_depth c3_kind c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))) ↔ ((shared_expr_Repair113_63 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair113_97 c3_depth c3_kind c3_sign r1_level))) := (iff_congr (normalization_7966 c3_depth c3_kind c3_sign r1_level) (normalization_8086 c3_depth c3_kind c3_sign r1_level))

-- Checked replay of trans.
theorem replay_7658 (c3_depth c3_kind c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))) := by
  classical
  have ht := (normalized_2430 (shared_expr_Repair113_63 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair113_96 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair113_97 c3_depth c3_kind c3_sign r1_level))
  have n0 : ((shared_expr_Repair113_63 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Repair113_96 c3_depth c3_kind c3_sign r1_level)) := by
    exact Iff.mp (normalization_8084 c3_depth c3_kind c3_sign r1_level) (replay_7656 c3_depth c3_kind c3_sign r1_level)
  have n1 : ((shared_expr_Repair113_96 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair113_97 c3_depth c3_kind c3_sign r1_level))) := by
    exact Iff.mp (normalization_8087 c3_depth c3_kind c3_sign r1_level) (replay_7657 c3_depth c3_kind c3_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8088 c3_depth c3_kind c3_sign r1_level) hn

end H4Formal.Generated.Repair
