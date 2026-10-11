import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair037

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair038_0 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ ((formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True))
abbrev formula_935 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_0 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_844 (p0 p1 : Prop) : (((p0 ↔ p1)) → ((p0 ↔ True) ↔ (p1 ↔ True))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_1 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
abbrev shared_expr_Repair038_2 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_3 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_2 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Repair038_4 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_5 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_4 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Repair038_6 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_7 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((shared_expr_Repair038_6 c0_depth c0_kind c0_sign r1_level) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_8 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_2 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_7 c0_depth c0_kind c0_node c0_sign r1_level)))
abbrev shared_expr_Repair038_9 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((shared_expr_Repair038_6 c0_depth c0_kind c0_sign r1_level) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_10 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_2 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_9 c0_depth c0_kind c0_node c0_sign r1_level)))
abbrev shared_expr_Repair038_11 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_12 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((shared_expr_Repair038_11 c0_depth c0_kind c0_sign r1_level) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_13 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_12 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_4 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Repair038_14 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((shared_expr_Repair038_11 c0_depth c0_kind c0_sign r1_level) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_15 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_14 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_4 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Repair038_16 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_3 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_5 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair038_8 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair038_10 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair038_13 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair038_15 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
abbrev shared_expr_Repair038_17 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_1 c0_group c0_level c0_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair038_16 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))
abbrev shared_expr_Repair038_18 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_19 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_20 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_18 c0_level r1_depth r1_kind r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_19 c0_level r1_depth r1_kind r1_sign)))
abbrev shared_expr_Repair038_21 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_22 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_23 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_21 c0_level r1_depth r1_kind r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_22 c0_level r1_depth r1_kind r1_sign)))
abbrev shared_expr_Repair038_24 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Repair038_18 c0_level r1_depth r1_kind r1_sign) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_25 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_24 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_26 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Repair038_18 c0_level r1_depth r1_kind r1_sign) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_27 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_26 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_28 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Repair038_22 c0_level r1_depth r1_kind r1_sign) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_29 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_28 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_30 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Repair038_22 c0_level r1_depth r1_kind r1_sign) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_31 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_30 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_32 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_mode) ≤ (0 : Int)) ∧ (¬ ((c0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_20 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((((c0_mode) ≤ (1 : Int)) ∧ (¬ ((c0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_23 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((((c0_mode) ≤ (2 : Int)) ∧ (¬ ((c0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair038_25 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (3 : Int)) ∧ (¬ ((c0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair038_27 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (4 : Int)) ∧ (¬ ((c0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair038_29 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (5 : Int)) ∧ (¬ ((c0_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair038_31 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Repair038_33 (c0_depth c0_kind h r1_kind : Int) : Prop := ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∧ (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair038_34 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_35 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ∧ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_36 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Repair038_34 c0_node c0_sign h r1_depth r1_node r1_sign) ∨ (shared_expr_Repair038_35 c0_node c0_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Repair038_37 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
abbrev shared_expr_Repair038_38 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
abbrev shared_expr_Repair038_39 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Repair038_37 c0_node c0_sign r1_node r1_sign) ∨ (shared_expr_Repair038_38 c0_node c0_sign r1_node r1_sign)))
abbrev shared_expr_Repair038_40 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair038_36 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (shared_expr_Repair038_39 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))
abbrev shared_expr_Repair038_41 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Repair038_40 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Repair038_42 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ (¬ (shared_expr_Repair038_33 c0_depth c0_kind h r1_kind))) ∨ (shared_expr_Repair038_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
abbrev shared_expr_Repair038_43 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_32 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair038_42 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Repair038_44 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_17 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair038_43 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_3367 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ ((shared_expr_Repair038_44 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) := (iff_congr (normalization_3304 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_305))

abbrev shared_expr_Repair038_45 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_46 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_2 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_45 c0_depth c0_kind c0_node c0_sign r1_level)))
abbrev shared_expr_Repair038_47 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_48 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_2 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_47 c0_depth c0_kind c0_node c0_sign r1_level)))
abbrev shared_expr_Repair038_49 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_50 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_49 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_4 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Repair038_51 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_52 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_51 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_4 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Repair038_53 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_3 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_5 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair038_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair038_48 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair038_50 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair038_52 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
abbrev shared_expr_Repair038_54 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_1 c0_group c0_level c0_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair038_53 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))
abbrev shared_expr_Repair038_55 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_56 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_55 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_57 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_58 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_57 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_59 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair038_60 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_59 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_61 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair038_62 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_61 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair038_63 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_mode) ≤ (0 : Int)) ∧ (¬ ((c0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_20 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((((c0_mode) ≤ (1 : Int)) ∧ (¬ ((c0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_23 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((((c0_mode) ≤ (2 : Int)) ∧ (¬ ((c0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair038_56 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (3 : Int)) ∧ (¬ ((c0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair038_58 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (4 : Int)) ∧ (¬ ((c0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair038_60 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (5 : Int)) ∧ (¬ ((c0_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair038_62 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Repair038_64 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Repair038_35 c0_node c0_sign h r1_depth r1_node r1_sign) ∨ (shared_expr_Repair038_34 c0_node c0_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Repair038_65 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair038_66 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Repair038_37 c0_node c0_sign r1_node r1_sign) ∨ (shared_expr_Repair038_65 c0_node c0_sign r1_node r1_sign)))
abbrev shared_expr_Repair038_67 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair038_64 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (shared_expr_Repair038_66 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))
abbrev shared_expr_Repair038_68 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Repair038_67 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Repair038_69 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ (¬ (shared_expr_Repair038_33 c0_depth c0_kind h r1_kind))) ∨ (shared_expr_Repair038_68 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
abbrev shared_expr_Repair038_70 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_63 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair038_69 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Repair038_71 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_54 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair038_70 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_3368 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ ((shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) := (iff_congr (normalization_3365 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_305))

abbrev shared_expr_Repair038_72 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((shared_expr_Repair038_44 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ ((shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True))
theorem normalization_3369 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_935 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_72 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_3367 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_3368 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair038_73 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair038_44 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem replay_2328 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_935 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_844 (shared_expr_Repair038_44 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : (shared_expr_Repair038_73 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
    exact Iff.mp (normalization_3366 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2327 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_3369 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Repair038_74 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ (formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_936 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_74 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_845 (p0 : Prop) : ((p0 ↔ True) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_75 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_3370 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_936 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_75 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_3368 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_3365 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2329 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_936 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_845 (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_3370 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Repair038_76 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ (formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_937 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_76 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_846 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_77 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((shared_expr_Repair038_44 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_3371 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_937 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_77 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_3367 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_3365 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of trans.
theorem replay_2330 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_937 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_846 ((shared_expr_Repair038_44 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ((shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : (shared_expr_Repair038_72 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
    exact Iff.mp (normalization_3369 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2328 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have n1 : (shared_expr_Repair038_75 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
    exact Iff.mp (normalization_3370 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2329 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3371 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_2331 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i162 : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2330 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) i162

theorem normalized_847 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3372 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : ((formula_931 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_931 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) ↔ ((shared_expr_Repair038_69 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair038_69 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) := (iff_congr (normalization_3363 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (normalization_3363 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2332 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : ((formula_931 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_931 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) := by
  classical
  have ht := (normalized_847 (shared_expr_Repair038_69 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_3372 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) hn

abbrev shared_expr_Repair038_78 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((formula_932 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_932 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
abbrev formula_938 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_78 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)

theorem normalized_848 (p0 p1 : Prop) : (((p0 ↔ p0)) → (p1 ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_79 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Repair038_70 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair038_70 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
theorem normalization_3373 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_938 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair038_79 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := (iff_congr (normalization_3364 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (normalization_3364 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2333 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_938 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := by
  classical
  have ht := (normalized_848 (shared_expr_Repair038_69 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (shared_expr_Repair038_70 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
  have n0 : ((shared_expr_Repair038_69 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair038_69 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) := by
    exact Iff.mp (normalization_3372 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (replay_2332 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_3373 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) hn

abbrev shared_expr_Repair038_80 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_939 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_80 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_849 (p0 p1 : Prop) : (((p0 ↔ p0)) → (p1 ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_81 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_3374 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_939 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_81 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_3365 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_3365 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2334 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_939 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_849 (shared_expr_Repair038_70 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : (shared_expr_Repair038_79 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := by
    exact Iff.mp (normalization_3373 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (replay_2333 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_3374 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_2335 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i162 : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2334 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2331 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i162)

theorem normalized_850 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of rewrite.
theorem replay_2336 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_939 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_850 (shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_3374 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_2337 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i162 : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2336 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2335 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i162)

-- Checked replay of mp.
theorem replay_2338 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i162 : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2334 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2337 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i162)

-- Checked replay of mp.
theorem replay_2339 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i162 : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2334 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2338 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i162)

abbrev shared_expr_Repair038_82 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ (c0_kind = (2 : Int))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))))))
abbrev formula_940 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair038_82 c0_depth c0_kind c0_sign r1_group r1_level)

abbrev shared_expr_Repair038_83 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ (c0_kind = (2 : Int))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))))))
abbrev formula_941 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair038_83 c0_depth c0_kind c0_sign r1_group r1_level)

abbrev shared_expr_Repair038_84 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int)))))
abbrev formula_942 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair038_84 c0_depth c0_kind c0_node c0_sign r1_group r1_level)

abbrev shared_expr_Repair038_85 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int)))))
abbrev formula_943 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair038_85 c0_depth c0_kind c0_node c0_sign r1_group r1_level)

abbrev shared_expr_Repair038_86 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int)))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))))))
abbrev formula_944 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair038_86 c0_depth c0_kind c0_node c0_sign r1_group r1_level)

abbrev shared_expr_Repair038_87 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int)))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))))))
abbrev formula_945 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair038_87 c0_depth c0_kind c0_node c0_sign r1_group r1_level)

abbrev shared_expr_Repair038_88 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (0 : Int)) ∧ (formula_940 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((r1_mode = (1 : Int)) ∧ (formula_941 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((r1_mode = (2 : Int)) ∧ (formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((r1_mode = (3 : Int)) ∧ (formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((r1_mode = (4 : Int)) ∧ (formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((r1_mode = (5 : Int)) ∧ (formula_945 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
abbrev formula_946 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair038_88 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

abbrev shared_expr_Repair038_89 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((c0_kind = (0 : Int)) ∧ ((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group)))) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (formula_946 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))
abbrev formula_947 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair038_89 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)

abbrev shared_expr_Repair038_90 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (((c0_group = (1 : Int)) ∧ ((r1_kind = (1 : Int)) ∧ (r1_depth = c0_level) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))))) ∨ ((¬ (c0_group = (1 : Int))) ∧ ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_level)) = (-1 : Int)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))))))
abbrev formula_948 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair038_90 c0_group c0_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair038_91 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (((c0_group = (1 : Int)) ∧ ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_level)) = (-1 : Int)) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))))) ∨ ((¬ (c0_group = (1 : Int))) ∧ ((r1_kind = (1 : Int)) ∧ (r1_depth = c0_level) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))))))
abbrev formula_949 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair038_91 c0_group c0_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair038_92 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((c0_mode = (0 : Int)) ∧ (formula_948 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((c0_mode = (1 : Int)) ∧ (formula_949 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((c0_mode = (2 : Int)) ∧ (formula_924 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c0_mode = (3 : Int)) ∧ (formula_925 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c0_mode = (4 : Int)) ∧ (formula_926 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c0_mode = (5 : Int)) ∧ (formula_927 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))
abbrev formula_950 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_92 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair038_93 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_sign = (0 : Int)) ∧ (c0_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∨ ((r1_sign = (2 : Int)) ∧ (c0_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∨ ((r1_sign = (1 : Int)) ∧ (c0_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)))))
abbrev formula_951 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_93 c0_node c0_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Repair038_94 (c0_node c0_sign r1_node r1_sign : Int) : Prop := ((((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c0_sign = (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ∨ (((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c0_sign = (1 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_952 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_94 c0_node c0_sign r1_node r1_sign)

abbrev shared_expr_Repair038_95 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((r1_kind = (2 : Int)) ∨ (c0_kind = (2 : Int)))) ∧ (((r1_depth = c0_depth) ∧ (formula_951 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ (formula_952 c0_node c0_sign r1_node r1_sign))))
abbrev shared_expr_Repair038_96 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind = (2 : Int)) ∨ (c0_kind = (2 : Int))) ∧ (¬ ((r1_kind = (2 : Int)) ∧ (c0_kind = (1 : Int)) ∧ (c0_depth = h)))) ∨ (shared_expr_Repair038_95 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
abbrev formula_953 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_96 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair038_97 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ (formula_950 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (formula_953 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev formula_954 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_97 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair038_98 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((r1_kind = (0 : Int)) ∧ (formula_947 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) ∨ ((¬ (r1_kind = (0 : Int))) ∧ (formula_954 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev formula_955 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_98 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair038_99 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_955 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_956 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair038_99 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

set_option maxHeartbeats 2000000 in
theorem normalized_851 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15))) ∧ (¬ ((p47 ∧ (¬ p35)) ∧ (p15 ∧ (¬ p2)) ∧ (p52 ∧ (¬ p53))))) ∨ ((¬ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)))) ∧ ((((¬ p54) ∧ p55) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p56)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p56)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p59)))) ∨ (((¬ p60) ∧ p54) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p61) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p62)))))))))))) ↔ (((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15))) ∧ (¬ ((p47 ∧ (¬ p35)) ∧ (p15 ∧ (¬ p2)) ∧ (p52 ∧ (¬ p53))))) ∨ ((¬ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)))) ∧ ((((¬ p54) ∧ p55) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p56)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p56)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p59)))) ∨ (((¬ p60) ∧ p54) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p61) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p62))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3375 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

abbrev shared_expr_Repair038_100 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
theorem normalization_3376 (c0_depth c0_kind c0_sign r1_level : Int) : ((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (shared_expr_Repair038_100 c0_depth c0_kind c0_sign r1_level) := (and_congr (normalization_142 c0_kind) (and_congr (normalization_3375 c0_depth r1_level) (normalization_146 c0_sign)))

abbrev shared_expr_Repair038_101 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_100 c0_depth c0_kind c0_sign r1_level)))
theorem normalization_3377 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (formula_940 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair038_101 c0_depth c0_kind c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_141 c0_kind)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_3376 c0_depth c0_kind c0_sign r1_level)))

theorem normalization_3378 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (0 : Int)) ∧ (formula_940 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_101 c0_depth c0_kind c0_sign r1_group r1_level)) := (and_congr (normalization_2771 r1_mode) (normalization_3377 c0_depth c0_kind c0_sign r1_group r1_level))

abbrev shared_expr_Repair038_102 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
theorem normalization_3379 (c0_depth c0_kind c0_sign r1_level : Int) : ((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (shared_expr_Repair038_102 c0_depth c0_kind c0_sign r1_level) := (and_congr (normalization_142 c0_kind) (and_congr (normalization_3375 c0_depth r1_level) (normalization_152 c0_sign)))

abbrev shared_expr_Repair038_103 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_102 c0_depth c0_kind c0_sign r1_level)))
theorem normalization_3380 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (formula_941 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair038_103 c0_depth c0_kind c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_141 c0_kind)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_3379 c0_depth c0_kind c0_sign r1_level)))

theorem normalization_3381 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (1 : Int)) ∧ (formula_941 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_103 c0_depth c0_kind c0_sign r1_group r1_level)) := (and_congr (normalization_3230 r1_mode) (normalization_3380 c0_depth c0_kind c0_sign r1_group r1_level))

abbrev shared_expr_Repair038_104 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_100 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_45 c0_depth c0_kind c0_node c0_sign r1_level)))
theorem normalization_3382 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair038_104 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_3376 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_3315 c0_depth c0_kind c0_node c0_sign r1_level)))

theorem normalization_3383 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (2 : Int)) ∧ (formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair038_104 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (and_congr (normalization_3234 r1_mode) (normalization_3382 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

abbrev shared_expr_Repair038_105 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_100 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_47 c0_depth c0_kind c0_node c0_sign r1_level)))
theorem normalization_3384 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair038_105 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_3376 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_3318 c0_depth c0_kind c0_node c0_sign r1_level)))

theorem normalization_3385 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (3 : Int)) ∧ (formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair038_105 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (and_congr (normalization_3240 r1_mode) (normalization_3384 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

abbrev shared_expr_Repair038_106 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_49 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_102 c0_depth c0_kind c0_sign r1_level)))
theorem normalization_3386 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair038_106 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_3321 c0_depth c0_kind c0_node c0_sign r1_level)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_3379 c0_depth c0_kind c0_sign r1_level)))

theorem normalization_3387 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (4 : Int)) ∧ (formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair038_106 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (and_congr (normalization_3244 r1_mode) (normalization_3386 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

abbrev shared_expr_Repair038_107 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_51 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair038_102 c0_depth c0_kind c0_sign r1_level)))
theorem normalization_3388 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_945 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair038_107 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2761 r1_group) (normalization_3324 c0_depth c0_kind c0_node c0_sign r1_level)) (and_congr (not_congr (normalization_2761 r1_group)) (normalization_3379 c0_depth c0_kind c0_sign r1_level)))

theorem normalization_3389 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (5 : Int)) ∧ (formula_945 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair038_107 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (and_congr (normalization_3249 r1_mode) (normalization_3388 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

abbrev shared_expr_Repair038_108 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_101 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_103 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair038_104 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair038_105 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair038_106 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair038_107 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
theorem normalization_3390 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_946 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair038_108 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (or_congr (normalization_3378 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (or_congr (normalization_3381 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (or_congr (normalization_3383 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (or_congr (normalization_3385 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (or_congr (normalization_3387 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3389 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))))))

abbrev shared_expr_Repair038_109 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_1 c0_group c0_level c0_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair038_108 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))
theorem normalization_3391 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_947 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair038_109 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_134 c0_kind) (normalization_3307 c0_group c0_level c0_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_134 c0_kind)) (normalization_3390 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))

theorem normalization_3392 (c0_level r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_level)) = (-1 : Int)) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_3393 (c0_level r1_depth r1_kind r1_sign : Int) : ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_level)) = (-1 : Int)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int)))) ↔ (shared_expr_Repair038_19 c0_level r1_depth r1_kind r1_sign) := (and_congr (normalization_2282 r1_kind) (and_congr (normalization_3392 c0_level r1_depth) (normalization_3256 r1_sign)))

theorem normalization_3394 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : (formula_948 c0_group c0_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Repair038_20 c0_group c0_level r1_depth r1_kind r1_sign) := (or_congr (and_congr (normalization_180 c0_group) (normalization_3257 c0_level r1_depth r1_kind r1_sign)) (and_congr (not_congr (normalization_180 c0_group)) (normalization_3393 c0_level r1_depth r1_kind r1_sign)))

theorem normalization_3395 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : ((c0_mode = (0 : Int)) ∧ (formula_948 c0_group c0_level r1_depth r1_kind r1_sign)) ↔ ((((c0_mode) ≤ (0 : Int)) ∧ (¬ ((c0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_20 c0_group c0_level r1_depth r1_kind r1_sign)) := (and_congr (normalization_179 c0_mode) (normalization_3394 c0_group c0_level r1_depth r1_kind r1_sign))

theorem normalization_3396 (c0_level r1_depth r1_kind r1_sign : Int) : ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_level)) = (-1 : Int)) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int)))) ↔ (shared_expr_Repair038_21 c0_level r1_depth r1_kind r1_sign) := (and_congr (normalization_2282 r1_kind) (and_congr (normalization_3392 c0_level r1_depth) (normalization_3262 r1_sign)))

theorem normalization_3397 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : (formula_949 c0_group c0_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Repair038_23 c0_group c0_level r1_depth r1_kind r1_sign) := (or_congr (and_congr (normalization_180 c0_group) (normalization_3396 c0_level r1_depth r1_kind r1_sign)) (and_congr (not_congr (normalization_180 c0_group)) (normalization_3264 c0_level r1_depth r1_kind r1_sign)))

theorem normalization_3398 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : ((c0_mode = (1 : Int)) ∧ (formula_949 c0_group c0_level r1_depth r1_kind r1_sign)) ↔ ((((c0_mode) ≤ (1 : Int)) ∧ (¬ ((c0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair038_23 c0_group c0_level r1_depth r1_kind r1_sign)) := (and_congr (normalization_191 c0_mode) (normalization_3397 c0_group c0_level r1_depth r1_kind r1_sign))

theorem normalization_3399 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (formula_950 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair038_63 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_3395 c0_group c0_level c0_mode r1_depth r1_kind r1_sign) (or_congr (normalization_3398 c0_group c0_level c0_mode r1_depth r1_kind r1_sign) (or_congr (normalization_3338 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (or_congr (normalization_3341 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (or_congr (normalization_3344 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (normalization_3347 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign))))))

theorem normalization_3400 (c0_node r1_node : Int) : ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)) ↔ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3401 (c0_node c0_sign r1_node r1_sign : Int) : ((r1_sign = (0 : Int)) ∧ (c0_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_2287 r1_sign) (and_congr (normalization_144 c0_sign) (normalization_3400 c0_node r1_node)))

theorem normalization_3402 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((r1_sign = (2 : Int)) ∧ (c0_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (shared_expr_Repair038_35 c0_node c0_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_2779 r1_sign) (and_congr (normalization_145 c0_sign) (and_congr (normalization_2778 h r1_depth) (normalization_3400 c0_node r1_node))))

theorem normalization_3403 (c0_node r1_node : Int) : ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3404 (c0_node r1_node : Int) : (¬ ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := (not_congr (normalization_3403 c0_node r1_node))

theorem normalization_3405 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((r1_sign = (1 : Int)) ∧ (c0_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair038_34 c0_node c0_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_2479 r1_sign) (and_congr (normalization_151 c0_sign) (and_congr (normalization_2850 h r1_depth) (normalization_3404 c0_node r1_node))))

theorem normalization_3406 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_951 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Repair038_64 c0_node c0_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_3401 c0_node c0_sign r1_node r1_sign) (or_congr (normalization_3402 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_3405 c0_node c0_sign h r1_depth r1_node r1_sign)))

theorem normalization_3407 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((r1_depth = c0_depth) ∧ (formula_951 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair038_64 c0_node c0_sign h r1_depth r1_node r1_sign)) := (and_congr (normalization_3285 c0_depth r1_depth) (normalization_3406 c0_node c0_sign h r1_depth r1_node r1_sign))

theorem normalization_3408 (c0_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3409 (c0_node r1_node : Int) : ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3410 (c0_node c0_sign r1_node r1_sign : Int) : (((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c0_sign = (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (shared_expr_Repair038_37 c0_node c0_sign r1_node r1_sign) := (and_congr (normalization_3256 r1_sign) (and_congr (normalization_144 c0_sign) (normalization_3409 c0_node r1_node)))

theorem normalization_3411 (c0_node r1_node : Int) : ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3412 (c0_node r1_node : Int) : (¬ ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_3411 c0_node r1_node))

theorem normalization_3413 (c0_node c0_sign r1_node r1_sign : Int) : (((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c0_sign = (1 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))) ↔ (shared_expr_Repair038_65 c0_node c0_sign r1_node r1_sign) := (and_congr (normalization_3262 r1_sign) (and_congr (normalization_151 c0_sign) (normalization_3412 c0_node r1_node)))

theorem normalization_3414 (c0_node c0_sign r1_node r1_sign : Int) : (formula_952 c0_node c0_sign r1_node r1_sign) ↔ ((shared_expr_Repair038_37 c0_node c0_sign r1_node r1_sign) ∨ (shared_expr_Repair038_65 c0_node c0_sign r1_node r1_sign)) := (or_congr (normalization_3410 c0_node c0_sign r1_node r1_sign) (normalization_3413 c0_node c0_sign r1_node r1_sign))

theorem normalization_3415 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : (((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ (formula_952 c0_node c0_sign r1_node r1_sign)) ↔ (shared_expr_Repair038_66 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) := (and_congr (normalization_3408 c0_depth r1_depth) (normalization_3414 c0_node c0_sign r1_node r1_sign))

theorem normalization_3416 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (((r1_depth = c0_depth) ∧ (formula_951 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ (formula_952 c0_node c0_sign r1_node r1_sign))) ↔ (shared_expr_Repair038_67 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_3407 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_3415 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))

theorem normalization_3417 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_953 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair038_69 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_3282 c0_kind r1_kind) (normalization_3284 c0_depth c0_kind h r1_kind)) (and_congr (not_congr (normalization_3282 c0_kind r1_kind)) (normalization_3416 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)))

theorem normalization_3418 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_954 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair038_70 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_134 c0_kind) (normalization_3399 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (and_congr (not_congr (normalization_134 c0_kind)) (normalization_3417 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair038_110 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair038_109 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair038_70 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_3419 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_955 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_110 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (and_congr (normalization_2270 r1_kind) (normalization_3391 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_2270 r1_kind)) (normalization_3418 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair038_111 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair038_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_110 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_3420 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_956 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair038_111 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_3365 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_3419 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2340 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_956 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_851 ((r1_kind) ≤ (0 : Int)) ((r1_kind) ≤ (-1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_kind) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ((r1_mode) ≤ (0 : Int)) ((r1_mode) ≤ (-1 : Int)) ((r1_group) ≤ (1 : Int)) ((r1_group) ≤ (0 : Int)) ((c0_kind) ≤ (2 : Int)) ((c0_kind) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c0_sign) ≤ (2 : Int)) ((c0_sign) ≤ (1 : Int)) ((r1_mode) ≤ (1 : Int)) ((r1_mode) ≤ (2 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) ((r1_mode) ≤ (3 : Int)) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int)) ((r1_mode) ≤ (4 : Int)) ((r1_mode) ≤ (5 : Int)) ((c0_mode) ≤ (0 : Int)) ((c0_mode) ≤ (-1 : Int)) ((c0_group) ≤ (1 : Int)) ((c0_group) ≤ (0 : Int)) ((r1_kind) ≤ (1 : Int)) ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)) ((r1_sign) ≤ (2 : Int)) ((r1_sign) ≤ (1 : Int)) ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ((c0_mode) ≤ (1 : Int)) ((c0_mode) ≤ (2 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((r1_kind) ≤ (2 : Int)) ((c0_mode) ≤ (3 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int)) ((c0_mode) ≤ (4 : Int)) ((c0_mode) ≤ (5 : Int)) ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3420 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_2341 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i162 : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_955 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2340 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2339 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i162)

theorem normalized_852 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3421 (c0_mode r1_mode : Int) : (r1_mode ≤ c0_mode) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3422 (c0_mode r1_mode : Int) : (r1_mode ≥ c0_mode) ↔ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_3423 (c0_mode r1_mode : Int) : ((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (and_congr (normalization_3421 c0_mode r1_mode) (normalization_3422 c0_mode r1_mode))

abbrev shared_expr_Repair038_112 (c0_mode r1_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
theorem normalization_3424 (c0_mode r1_mode : Int) : ((r1_mode = c0_mode) ↔ ((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode))) ↔ (shared_expr_Repair038_112 c0_mode r1_mode) := (iff_congr (normalization_3222 c0_mode r1_mode) (normalization_3423 c0_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_2342 (c0_mode r1_mode : Int) : ((r1_mode = c0_mode) ↔ ((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode))) := by
  classical
  have ht := (normalized_852 ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3424 c0_mode r1_mode) hn

theorem normalized_853 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3425 (c0_mode r1_mode : Int) : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3426 (c0_mode r1_mode : Int) : ((r1_mode ≤ c0_mode) ↔ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ↔ ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_3421 c0_mode r1_mode) (normalization_3425 c0_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_2343 (c0_mode r1_mode : Int) : ((r1_mode ≤ c0_mode) ↔ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_853 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3426 c0_mode r1_mode) hn

theorem normalized_854 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3427 (c0_mode r1_mode : Int) : ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_3428 (c0_mode r1_mode : Int) : ((r1_mode ≥ c0_mode) ↔ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ (((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (iff_congr (normalization_3422 c0_mode r1_mode) (normalization_3427 c0_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_2344 (c0_mode r1_mode : Int) : ((r1_mode ≥ c0_mode) ↔ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_854 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3428 c0_mode r1_mode) hn

theorem normalized_855 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3429 (c0_mode r1_mode : Int) : (((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (and_congr (normalization_3425 c0_mode r1_mode) (normalization_3427 c0_mode r1_mode))

theorem normalization_3430 (c0_mode r1_mode : Int) : (((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ (((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Repair038_112 c0_mode r1_mode) := (iff_congr (normalization_3423 c0_mode r1_mode) (normalization_3429 c0_mode r1_mode))

-- Checked replay of monotonicity.
theorem replay_2345 (c0_mode r1_mode : Int) : (((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ (((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_855 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3426 c0_mode r1_mode) (replay_2343 c0_mode r1_mode)
  have n1 : (((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_3428 c0_mode r1_mode) (replay_2344 c0_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3430 c0_mode r1_mode) hn

abbrev shared_expr_Repair038_113 (c0_mode r1_mode : Int) : Prop := ((((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))))
abbrev formula_957 (c0_mode r1_mode : Int) : Prop := (shared_expr_Repair038_113 c0_mode r1_mode)

theorem normalized_856 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3431 (c0_mode r1_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_3425 c0_mode r1_mode))

theorem normalization_3432 (c0_mode r1_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (not_congr (normalization_3427 c0_mode r1_mode))

theorem normalization_3433 (c0_mode r1_mode : Int) : ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))) := (or_congr (normalization_3431 c0_mode r1_mode) (normalization_3432 c0_mode r1_mode))

theorem normalization_3434 (c0_mode r1_mode : Int) : (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) := (not_congr (normalization_3433 c0_mode r1_mode))

abbrev shared_expr_Repair038_114 (c0_mode r1_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))))
theorem normalization_3435 (c0_mode r1_mode : Int) : (formula_957 c0_mode r1_mode) ↔ (shared_expr_Repair038_114 c0_mode r1_mode) := (iff_congr (normalization_3429 c0_mode r1_mode) (normalization_3434 c0_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_2346 (c0_mode r1_mode : Int) : (formula_957 c0_mode r1_mode) := by
  classical
  have ht := (normalized_856 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3435 c0_mode r1_mode) hn

theorem normalized_857 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3436 (c0_mode r1_mode : Int) : (((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair038_114 c0_mode r1_mode) := (iff_congr (normalization_3423 c0_mode r1_mode) (normalization_3434 c0_mode r1_mode))

-- Checked replay of trans.
theorem replay_2347 (c0_mode r1_mode : Int) : (((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_857 ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) (shared_expr_Repair038_114 c0_mode r1_mode))
  have n0 : (shared_expr_Repair038_112 c0_mode r1_mode) := by
    exact Iff.mp (normalization_3430 c0_mode r1_mode) (replay_2345 c0_mode r1_mode)
  have n1 : (shared_expr_Repair038_114 c0_mode r1_mode) := by
    exact Iff.mp (normalization_3435 c0_mode r1_mode) (replay_2346 c0_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3436 c0_mode r1_mode) hn

theorem normalized_858 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3437 (c0_mode r1_mode : Int) : ((r1_mode = c0_mode) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair038_114 c0_mode r1_mode) := (iff_congr (normalization_3222 c0_mode r1_mode) (normalization_3434 c0_mode r1_mode))

-- Checked replay of trans.
theorem replay_2348 (c0_mode r1_mode : Int) : ((r1_mode = c0_mode) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_858 ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) (shared_expr_Repair038_114 c0_mode r1_mode))
  have n0 : (shared_expr_Repair038_112 c0_mode r1_mode) := by
    exact Iff.mp (normalization_3424 c0_mode r1_mode) (replay_2342 c0_mode r1_mode)
  have n1 : (shared_expr_Repair038_114 c0_mode r1_mode) := by
    exact Iff.mp (normalization_3436 c0_mode r1_mode) (replay_2347 c0_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3437 c0_mode r1_mode) hn

theorem normalized_859 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3438 (c0_level r1_level : Int) : (r1_level ≤ c0_level) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3439 (c0_level r1_level : Int) : (r1_level ≥ c0_level) ↔ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_3440 (c0_level r1_level : Int) : ((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (and_congr (normalization_3438 c0_level r1_level) (normalization_3439 c0_level r1_level))

abbrev shared_expr_Repair038_115 (c0_level r1_level : Int) : Prop := (((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
theorem normalization_3441 (c0_level r1_level : Int) : ((r1_level = c0_level) ↔ ((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level))) ↔ (shared_expr_Repair038_115 c0_level r1_level) := (iff_congr (normalization_3223 c0_level r1_level) (normalization_3440 c0_level r1_level))

-- Checked replay of rewrite.
theorem replay_2349 (c0_level r1_level : Int) : ((r1_level = c0_level) ↔ ((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level))) := by
  classical
  have ht := (normalized_859 ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3441 c0_level r1_level) hn

theorem normalized_860 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3442 (c0_level r1_level : Int) : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3443 (c0_level r1_level : Int) : ((r1_level ≤ c0_level) ↔ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_3438 c0_level r1_level) (normalization_3442 c0_level r1_level))

-- Checked replay of rewrite.
theorem replay_2350 (c0_level r1_level : Int) : ((r1_level ≤ c0_level) ↔ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_860 ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3443 c0_level r1_level) hn

theorem normalized_861 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3444 (c0_level r1_level : Int) : ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_3445 (c0_level r1_level : Int) : ((r1_level ≥ c0_level) ↔ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (iff_congr (normalization_3439 c0_level r1_level) (normalization_3444 c0_level r1_level))

-- Checked replay of rewrite.
theorem replay_2351 (c0_level r1_level : Int) : ((r1_level ≥ c0_level) ↔ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_861 ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3445 c0_level r1_level) hn

theorem normalized_862 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3446 (c0_level r1_level : Int) : (((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (and_congr (normalization_3442 c0_level r1_level) (normalization_3444 c0_level r1_level))

theorem normalization_3447 (c0_level r1_level : Int) : (((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ (((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) ↔ (shared_expr_Repair038_115 c0_level r1_level) := (iff_congr (normalization_3440 c0_level r1_level) (normalization_3446 c0_level r1_level))

-- Checked replay of monotonicity.
theorem replay_2352 (c0_level r1_level : Int) : (((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ (((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_862 ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3443 c0_level r1_level) (replay_2350 c0_level r1_level)
  have n1 : (((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_3445 c0_level r1_level) (replay_2351 c0_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3447 c0_level r1_level) hn

abbrev shared_expr_Repair038_116 (c0_level r1_level : Int) : Prop := ((((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))))
abbrev formula_958 (c0_level r1_level : Int) : Prop := (shared_expr_Repair038_116 c0_level r1_level)

theorem normalized_863 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3448 (c0_level r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_3442 c0_level r1_level))

theorem normalization_3449 (c0_level r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_3444 c0_level r1_level))

theorem normalization_3450 (c0_level r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) := (or_congr (normalization_3448 c0_level r1_level) (normalization_3449 c0_level r1_level))

theorem normalization_3451 (c0_level r1_level : Int) : (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) := (not_congr (normalization_3450 c0_level r1_level))

abbrev shared_expr_Repair038_117 (c0_level r1_level : Int) : Prop := (((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))))
theorem normalization_3452 (c0_level r1_level : Int) : (formula_958 c0_level r1_level) ↔ (shared_expr_Repair038_117 c0_level r1_level) := (iff_congr (normalization_3446 c0_level r1_level) (normalization_3451 c0_level r1_level))

-- Checked replay of rewrite.
theorem replay_2353 (c0_level r1_level : Int) : (formula_958 c0_level r1_level) := by
  classical
  have ht := (normalized_863 ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3452 c0_level r1_level) hn

theorem normalized_864 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3453 (c0_level r1_level : Int) : (((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair038_117 c0_level r1_level) := (iff_congr (normalization_3440 c0_level r1_level) (normalization_3451 c0_level r1_level))

-- Checked replay of trans.
theorem replay_2354 (c0_level r1_level : Int) : (((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_864 ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) (shared_expr_Repair038_117 c0_level r1_level))
  have n0 : (shared_expr_Repair038_115 c0_level r1_level) := by
    exact Iff.mp (normalization_3447 c0_level r1_level) (replay_2352 c0_level r1_level)
  have n1 : (shared_expr_Repair038_117 c0_level r1_level) := by
    exact Iff.mp (normalization_3452 c0_level r1_level) (replay_2353 c0_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3453 c0_level r1_level) hn

theorem normalized_865 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3454 (c0_level r1_level : Int) : ((r1_level = c0_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair038_117 c0_level r1_level) := (iff_congr (normalization_3223 c0_level r1_level) (normalization_3451 c0_level r1_level))

-- Checked replay of trans.
theorem replay_2355 (c0_level r1_level : Int) : ((r1_level = c0_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_865 ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) (shared_expr_Repair038_117 c0_level r1_level))
  have n0 : (shared_expr_Repair038_115 c0_level r1_level) := by
    exact Iff.mp (normalization_3441 c0_level r1_level) (replay_2349 c0_level r1_level)
  have n1 : (shared_expr_Repair038_117 c0_level r1_level) := by
    exact Iff.mp (normalization_3453 c0_level r1_level) (replay_2354 c0_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3454 c0_level r1_level) hn

theorem normalized_866 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3455 (c0_group r1_group : Int) : (r1_group ≤ c0_group) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3456 (c0_group r1_group : Int) : (r1_group ≥ c0_group) ↔ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_3457 (c0_group r1_group : Int) : ((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (and_congr (normalization_3455 c0_group r1_group) (normalization_3456 c0_group r1_group))

abbrev shared_expr_Repair038_118 (c0_group r1_group : Int) : Prop := (((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
theorem normalization_3458 (c0_group r1_group : Int) : ((r1_group = c0_group) ↔ ((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group))) ↔ (shared_expr_Repair038_118 c0_group r1_group) := (iff_congr (normalization_3305 c0_group r1_group) (normalization_3457 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2356 (c0_group r1_group : Int) : ((r1_group = c0_group) ↔ ((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group))) := by
  classical
  have ht := (normalized_866 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3458 c0_group r1_group) hn

theorem normalized_867 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3459 (c0_group r1_group : Int) : ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3460 (c0_group r1_group : Int) : ((r1_group ≤ c0_group) ↔ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_3455 c0_group r1_group) (normalization_3459 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2357 (c0_group r1_group : Int) : ((r1_group ≤ c0_group) ↔ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_867 ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3460 c0_group r1_group) hn

theorem normalized_868 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3461 (c0_group r1_group : Int) : ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_3462 (c0_group r1_group : Int) : ((r1_group ≥ c0_group) ↔ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (iff_congr (normalization_3456 c0_group r1_group) (normalization_3461 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2358 (c0_group r1_group : Int) : ((r1_group ≥ c0_group) ↔ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_868 ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3462 c0_group r1_group) hn

theorem normalized_869 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3463 (c0_group r1_group : Int) : (((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (and_congr (normalization_3459 c0_group r1_group) (normalization_3461 c0_group r1_group))

theorem normalization_3464 (c0_group r1_group : Int) : (((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ (((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) ↔ (shared_expr_Repair038_118 c0_group r1_group) := (iff_congr (normalization_3457 c0_group r1_group) (normalization_3463 c0_group r1_group))

-- Checked replay of monotonicity.
theorem replay_2359 (c0_group r1_group : Int) : (((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ (((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_869 ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3460 c0_group r1_group) (replay_2357 c0_group r1_group)
  have n1 : (((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_3462 c0_group r1_group) (replay_2358 c0_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3464 c0_group r1_group) hn

abbrev shared_expr_Repair038_119 (c0_group r1_group : Int) : Prop := ((((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))
abbrev formula_959 (c0_group r1_group : Int) : Prop := (shared_expr_Repair038_119 c0_group r1_group)

theorem normalized_870 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3465 (c0_group r1_group : Int) : (¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_3459 c0_group r1_group))

theorem normalization_3466 (c0_group r1_group : Int) : (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (not_congr (normalization_3461 c0_group r1_group))

theorem normalization_3467 (c0_group r1_group : Int) : ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) := (or_congr (normalization_3465 c0_group r1_group) (normalization_3466 c0_group r1_group))

theorem normalization_3468 (c0_group r1_group : Int) : (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))) := (not_congr (normalization_3467 c0_group r1_group))

abbrev shared_expr_Repair038_120 (c0_group r1_group : Int) : Prop := (((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_3469 (c0_group r1_group : Int) : (formula_959 c0_group r1_group) ↔ (shared_expr_Repair038_120 c0_group r1_group) := (iff_congr (normalization_3463 c0_group r1_group) (normalization_3468 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2360 (c0_group r1_group : Int) : (formula_959 c0_group r1_group) := by
  classical
  have ht := (normalized_870 ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3469 c0_group r1_group) hn

theorem normalized_871 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3470 (c0_group r1_group : Int) : (((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair038_120 c0_group r1_group) := (iff_congr (normalization_3457 c0_group r1_group) (normalization_3468 c0_group r1_group))

-- Checked replay of trans.
theorem replay_2361 (c0_group r1_group : Int) : (((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_871 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) (shared_expr_Repair038_120 c0_group r1_group))
  have n0 : (shared_expr_Repair038_118 c0_group r1_group) := by
    exact Iff.mp (normalization_3464 c0_group r1_group) (replay_2359 c0_group r1_group)
  have n1 : (shared_expr_Repair038_120 c0_group r1_group) := by
    exact Iff.mp (normalization_3469 c0_group r1_group) (replay_2360 c0_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3470 c0_group r1_group) hn

theorem normalized_872 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3471 (c0_group r1_group : Int) : ((r1_group = c0_group) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair038_120 c0_group r1_group) := (iff_congr (normalization_3305 c0_group r1_group) (normalization_3468 c0_group r1_group))

-- Checked replay of trans.
theorem replay_2362 (c0_group r1_group : Int) : ((r1_group = c0_group) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_872 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) (shared_expr_Repair038_120 c0_group r1_group))
  have n0 : (shared_expr_Repair038_118 c0_group r1_group) := by
    exact Iff.mp (normalization_3458 c0_group r1_group) (replay_2356 c0_group r1_group)
  have n1 : (shared_expr_Repair038_120 c0_group r1_group) := by
    exact Iff.mp (normalization_3470 c0_group r1_group) (replay_2361 c0_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3471 c0_group r1_group) hn

theorem normalized_873 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3472 (c0_group r1_group : Int) : (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))) := (not_congr (normalization_3468 c0_group r1_group))

abbrev shared_expr_Repair038_121 (c0_group r1_group : Int) : Prop := ((¬ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))))
theorem normalization_3473 (c0_group r1_group : Int) : ((¬ (r1_group = c0_group)) ↔ (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Repair038_121 c0_group r1_group) := (iff_congr (normalization_3306 c0_group r1_group) (normalization_3472 c0_group r1_group))

-- Checked replay of monotonicity.
theorem replay_2363 (c0_group r1_group : Int) : ((¬ (r1_group = c0_group)) ↔ (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_873 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair038_120 c0_group r1_group) := by
    exact Iff.mp (normalization_3471 c0_group r1_group) (replay_2362 c0_group r1_group)
  have hn := ht n0
  exact Iff.mpr (normalization_3473 c0_group r1_group) hn

abbrev shared_expr_Repair038_122 (c0_group r1_group : Int) : Prop := ((¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))
abbrev formula_960 (c0_group r1_group : Int) : Prop := (shared_expr_Repair038_122 c0_group r1_group)

theorem normalized_874 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_123 (c0_group r1_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_3474 (c0_group r1_group : Int) : (formula_960 c0_group r1_group) ↔ (shared_expr_Repair038_123 c0_group r1_group) := (iff_congr (normalization_3472 c0_group r1_group) (normalization_3467 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2364 (c0_group r1_group : Int) : (formula_960 c0_group r1_group) := by
  classical
  have ht := (normalized_874 ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3474 c0_group r1_group) hn

theorem normalized_875 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_124 (c0_group r1_group : Int) : Prop := ((¬ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_3475 (c0_group r1_group : Int) : ((¬ (r1_group = c0_group)) ↔ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) ↔ (shared_expr_Repair038_124 c0_group r1_group) := (iff_congr (normalization_3306 c0_group r1_group) (normalization_3467 c0_group r1_group))

-- Checked replay of trans.
theorem replay_2365 (c0_group r1_group : Int) : ((¬ (r1_group = c0_group)) ↔ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_875 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair038_121 c0_group r1_group) := by
    exact Iff.mp (normalization_3473 c0_group r1_group) (replay_2363 c0_group r1_group)
  have n1 : (shared_expr_Repair038_123 c0_group r1_group) := by
    exact Iff.mp (normalization_3474 c0_group r1_group) (replay_2364 c0_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3475 c0_group r1_group) hn

abbrev shared_expr_Repair038_125 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))) ∧ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))
abbrev formula_961 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair038_125 c0_group c0_level c0_mode r1_group r1_level r1_mode)

theorem normalized_876 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_126 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_3476 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (formula_961 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair038_126 c0_group c0_level c0_mode r1_group r1_level r1_mode) := (and_congr (normalization_3434 c0_mode r1_mode) (and_congr (normalization_3451 c0_level r1_level) (normalization_3467 c0_group r1_group)))

theorem normalization_3477 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group))) ↔ (formula_961 c0_group c0_level c0_mode r1_group r1_level r1_mode)) ↔ ((shared_expr_Repair038_1 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair038_126 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := (iff_congr (normalization_3307 c0_group c0_level c0_mode r1_group r1_level r1_mode) (normalization_3476 c0_group c0_level c0_mode r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_2366 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group))) ↔ (formula_961 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := by
  classical
  have ht := (normalized_876 ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))) ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair038_114 c0_mode r1_mode) := by
    exact Iff.mp (normalization_3437 c0_mode r1_mode) (replay_2348 c0_mode r1_mode)
  have n1 : (shared_expr_Repair038_117 c0_level r1_level) := by
    exact Iff.mp (normalization_3454 c0_level r1_level) (replay_2355 c0_level r1_level)
  have n2 : (shared_expr_Repair038_124 c0_group r1_group) := by
    exact Iff.mp (normalization_3475 c0_group r1_group) (replay_2365 c0_group r1_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3477 c0_group c0_level c0_mode r1_group r1_level r1_mode) hn

theorem normalized_877 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair038_127 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_3478 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair038_127 c0_group c0_level c0_mode r1_group r1_level r1_mode) := (or_congr (normalization_3431 c0_mode r1_mode) (or_congr (normalization_3432 c0_mode r1_mode) (or_congr (normalization_3448 c0_level r1_level) (or_congr (normalization_3449 c0_level r1_level) (normalization_3468 c0_group r1_group)))))

theorem normalization_3479 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (¬ (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode)) ↔ (¬ (shared_expr_Repair038_127 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := (not_congr (normalization_3478 c0_group c0_level c0_mode r1_group r1_level r1_mode))

theorem normalization_3480 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : ((formula_961 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode))) ↔ ((shared_expr_Repair038_126 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Repair038_127 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := (iff_congr (normalization_3476 c0_group c0_level c0_mode r1_group r1_level r1_mode) (normalization_3479 c0_group c0_level c0_mode r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_2367 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : ((formula_961 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := by
  classical
  have ht := (normalized_877 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3480 c0_group c0_level c0_mode r1_group r1_level r1_mode) hn

theorem normalized_878 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3481 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group))) ↔ (¬ (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode))) ↔ ((shared_expr_Repair038_1 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Repair038_127 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := (iff_congr (normalization_3307 c0_group c0_level c0_mode r1_group r1_level r1_mode) (normalization_3479 c0_group c0_level c0_mode r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_2368 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group))) ↔ (¬ (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := by
  classical
  have ht := (normalized_878 (shared_expr_Repair038_1 c0_group c0_level c0_mode r1_group r1_level r1_mode) (shared_expr_Repair038_126 c0_group c0_level c0_mode r1_group r1_level r1_mode) (shared_expr_Repair038_127 c0_group c0_level c0_mode r1_group r1_level r1_mode))
  have n0 : ((shared_expr_Repair038_1 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair038_126 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := by
    exact Iff.mp (normalization_3477 c0_group c0_level c0_mode r1_group r1_level r1_mode) (replay_2366 c0_group c0_level c0_mode r1_group r1_level r1_mode)
  have n1 : ((shared_expr_Repair038_126 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Repair038_127 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := by
    exact Iff.mp (normalization_3480 c0_group c0_level c0_mode r1_group r1_level r1_mode) (replay_2367 c0_group c0_level c0_mode r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3481 c0_group c0_level c0_mode r1_group r1_level r1_mode) hn

theorem normalized_879 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3482 (r1_mode : Int) : ((r1_mode ≤ (0 : Int)) ∧ (r1_mode ≥ (0 : Int))) ↔ (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) := (and_congr (normalization_2808 r1_mode) (normalization_2757 r1_mode))

theorem normalization_3483 (r1_mode : Int) : ((r1_mode = (0 : Int)) ↔ ((r1_mode ≤ (0 : Int)) ∧ (r1_mode ≥ (0 : Int)))) ↔ ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ↔ (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int))))) := (iff_congr (normalization_2771 r1_mode) (normalization_3482 r1_mode))

-- Checked replay of rewrite.
theorem replay_2369 (r1_mode : Int) : ((r1_mode = (0 : Int)) ↔ ((r1_mode ≤ (0 : Int)) ∧ (r1_mode ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_879 (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3483 r1_mode) hn

theorem normalized_880 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3484 (r1_mode : Int) : ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int)))) ↔ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))) := (or_congr (normalization_2809 r1_mode) (normalization_2807 r1_mode))

theorem normalization_3485 (r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) := (not_congr (normalization_3484 r1_mode))

theorem normalization_3486 (r1_mode : Int) : (((r1_mode ≤ (0 : Int)) ∧ (r1_mode ≥ (0 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int)))))) ↔ ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))))) := (iff_congr (normalization_3482 r1_mode) (normalization_3485 r1_mode))

-- Checked replay of rewrite.
theorem replay_2370 (r1_mode : Int) : (((r1_mode ≤ (0 : Int)) ∧ (r1_mode ≥ (0 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_880 ((r1_mode) ≤ (0 : Int)) ((r1_mode) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3486 r1_mode) hn

end H4Formal.Generated.Repair
