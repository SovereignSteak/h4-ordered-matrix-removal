import H4Formal.BooleanReplaySupport
import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair046

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_1075 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of rewrite.
abbrev shared_expr_Repair047_0 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
abbrev shared_expr_Repair047_1 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_2 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_1 c2_depth c2_kind c2_sign r3_level)))
abbrev shared_expr_Repair047_3 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_4 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_3 c2_depth c2_kind c2_sign r3_level)))
abbrev shared_expr_Repair047_5 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair047_6 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_1 c2_depth c2_kind c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_5 c2_depth c2_kind c2_node c2_sign r3_level)))
abbrev shared_expr_Repair047_7 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair047_8 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_1 c2_depth c2_kind c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_7 c2_depth c2_kind c2_node c2_sign r3_level)))
abbrev shared_expr_Repair047_9 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair047_10 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_9 c2_depth c2_kind c2_node c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_3 c2_depth c2_kind c2_sign r3_level)))
abbrev shared_expr_Repair047_11 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair047_12 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_11 c2_depth c2_kind c2_node c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_3 c2_depth c2_kind c2_sign r3_level)))
abbrev shared_expr_Repair047_13 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_2 c2_depth c2_kind c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_4 c2_depth c2_kind c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair047_6 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair047_8 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair047_10 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair047_12 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))
abbrev shared_expr_Repair047_14 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_0 c2_group c2_level c2_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair047_13 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Repair047_15 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_16 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_17 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_15 c2_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_16 c2_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Repair047_18 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_19 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_20 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_18 c2_level r3_depth r3_kind r3_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_19 c2_level r3_depth r3_kind r3_sign)))
abbrev shared_expr_Repair047_21 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair047_22 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_21 c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_23 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair047_24 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_23 c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_25 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair047_26 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_25 c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_27 (c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair047_28 (c2_group c2_level r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_27 c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c2_group) ≤ (1 : Int)) ∧ (¬ ((c2_group) ≤ (0 : Int))))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair047_29 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c2_mode) ≤ (0 : Int)) ∧ (¬ ((c2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_17 c2_group c2_level r3_depth r3_kind r3_sign)) ∨ ((((c2_mode) ≤ (1 : Int)) ∧ (¬ ((c2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_20 c2_group c2_level r3_depth r3_kind r3_sign)) ∨ ((((c2_mode) ≤ (2 : Int)) ∧ (¬ ((c2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair047_22 c2_group c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c2_mode) ≤ (3 : Int)) ∧ (¬ ((c2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair047_24 c2_group c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c2_mode) ≤ (4 : Int)) ∧ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair047_26 c2_group c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((((c2_mode) ≤ (5 : Int)) ∧ (¬ ((c2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair047_28 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Repair047_30 (c2_depth c2_kind h r3_kind : Int) : Prop := ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair047_31 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) ∧ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair047_32 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair047_33 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Repair047_31 c2_node c2_sign h r3_depth r3_node r3_sign) ∨ (shared_expr_Repair047_32 c2_node c2_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair047_34 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
abbrev shared_expr_Repair047_35 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) ∨ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair047_36 (c2_depth c2_node c2_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Repair047_34 c2_node c2_sign r3_node r3_sign) ∨ (shared_expr_Repair047_35 c2_node c2_sign r3_node r3_sign)))
abbrev shared_expr_Repair047_37 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair047_33 c2_node c2_sign h r3_depth r3_node r3_sign)) ∨ (shared_expr_Repair047_36 c2_depth c2_node c2_sign r3_depth r3_node r3_sign))
abbrev shared_expr_Repair047_38 (c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Repair047_37 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign))
abbrev shared_expr_Repair047_39 (c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (¬ (shared_expr_Repair047_30 c2_depth c2_kind h r3_kind))) ∨ (shared_expr_Repair047_38 c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign))
abbrev shared_expr_Repair047_40 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_29 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair047_39 c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev shared_expr_Repair047_41 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_14 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair047_40 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)))
theorem replay_2689 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1315 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_1075 (shared_expr_Repair047_41 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_4497 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_2690 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i178 : ((formula_1289 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1309 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_2689 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_2688 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i178)

-- Checked replay of mp.
theorem replay_2691 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i178 : ((formula_1289 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1309 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_2687 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_2690 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i178)

-- Checked replay of mp.
theorem replay_2692 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i178 : ((formula_1289 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1309 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_2687 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_2691 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i178)

abbrev shared_expr_Repair047_42 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ (c2_kind = (2 : Int))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))))))
abbrev formula_1316 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair047_42 c2_depth c2_kind c2_sign r3_group r3_level)

abbrev shared_expr_Repair047_43 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ (c2_kind = (2 : Int))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))))))
abbrev formula_1317 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair047_43 c2_depth c2_kind c2_sign r3_group r3_level)

abbrev shared_expr_Repair047_44 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c2_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ (c2_depth = r3_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int)))))
abbrev formula_1318 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair047_44 c2_depth c2_kind c2_node c2_sign r3_group r3_level)

abbrev shared_expr_Repair047_45 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c2_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ (c2_depth = r3_level) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int)))))
abbrev formula_1319 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair047_45 c2_depth c2_kind c2_node c2_sign r3_group r3_level)

abbrev shared_expr_Repair047_46 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c2_kind = (1 : Int)) ∧ (c2_depth = r3_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (0 : Int)))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))))))
abbrev formula_1320 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair047_46 c2_depth c2_kind c2_node c2_sign r3_group r3_level)

abbrev shared_expr_Repair047_47 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((r3_group = (1 : Int)) ∧ ((c2_kind = (1 : Int)) ∧ (c2_depth = r3_level) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))) ∧ ((c2_node % (2 : Int)) = (1 : Int)))) ∨ ((¬ (r3_group = (1 : Int))) ∧ ((c2_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int))))))
abbrev formula_1321 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (shared_expr_Repair047_47 c2_depth c2_kind c2_node c2_sign r3_group r3_level)

abbrev shared_expr_Repair047_48 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((r3_mode = (0 : Int)) ∧ (formula_1316 c2_depth c2_kind c2_sign r3_group r3_level)) ∨ ((r3_mode = (1 : Int)) ∧ (formula_1317 c2_depth c2_kind c2_sign r3_group r3_level)) ∨ ((r3_mode = (2 : Int)) ∧ (formula_1318 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((r3_mode = (3 : Int)) ∧ (formula_1319 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((r3_mode = (4 : Int)) ∧ (formula_1320 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((r3_mode = (5 : Int)) ∧ (formula_1321 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))
abbrev formula_1322 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair047_48 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)

abbrev shared_expr_Repair047_49 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((c2_kind = (0 : Int)) ∧ ((r3_mode = c2_mode) ∧ (r3_level = c2_level) ∧ (¬ (r3_group = c2_group)))) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_1322 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))
abbrev formula_1323 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair047_49 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)

abbrev shared_expr_Repair047_50 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := (((c2_group = (1 : Int)) ∧ ((r3_kind = (1 : Int)) ∧ (r3_depth = c2_level) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))))) ∨ ((¬ (c2_group = (1 : Int))) ∧ ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))))))
abbrev formula_1324 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair047_50 c2_group c2_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair047_51 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := (((c2_group = (1 : Int)) ∧ ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))))) ∨ ((¬ (c2_group = (1 : Int))) ∧ ((r3_kind = (1 : Int)) ∧ (r3_depth = c2_level) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))))))
abbrev formula_1325 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair047_51 c2_group c2_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair047_52 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((c2_mode = (0 : Int)) ∧ (formula_1324 c2_group c2_level r3_depth r3_kind r3_sign)) ∨ ((c2_mode = (1 : Int)) ∧ (formula_1325 c2_group c2_level r3_depth r3_kind r3_sign)) ∨ ((c2_mode = (2 : Int)) ∧ (formula_1300 c2_group c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c2_mode = (3 : Int)) ∧ (formula_1301 c2_group c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c2_mode = (4 : Int)) ∧ (formula_1302 c2_group c2_level r3_depth r3_kind r3_node r3_sign)) ∨ ((c2_mode = (5 : Int)) ∧ (formula_1303 c2_group c2_level r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1326 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair047_52 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair047_53 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (((r3_sign = (0 : Int)) ∧ (c2_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ ((r3_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ ((r3_sign = (1 : Int)) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))
abbrev formula_1327 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair047_53 c2_node c2_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Repair047_54 (c2_node c2_sign r3_node r3_sign : Int) : Prop := ((((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c2_sign = (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ∨ (((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_1328 (c2_node c2_sign r3_node r3_sign : Int) : Prop := (shared_expr_Repair047_54 c2_node c2_sign r3_node r3_sign)

abbrev shared_expr_Repair047_55 (c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r3_kind = (2 : Int)) ∨ (c2_kind = (2 : Int)))) ∧ (((r3_depth = c2_depth) ∧ (formula_1327 c2_node c2_sign h r3_depth r3_node r3_sign)) ∨ (((r3_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1328 c2_node c2_sign r3_node r3_sign))))
abbrev shared_expr_Repair047_56 (c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((((r3_kind = (2 : Int)) ∨ (c2_kind = (2 : Int))) ∧ (¬ ((r3_kind = (2 : Int)) ∧ (c2_kind = (1 : Int)) ∧ (c2_depth = h)))) ∨ (shared_expr_Repair047_55 c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign))
abbrev formula_1329 (c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair047_56 c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair047_57 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((c2_kind = (0 : Int)) ∧ (formula_1326 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_1329 c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1330 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair047_57 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)

abbrev shared_expr_Repair047_58 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((r3_kind = (0 : Int)) ∧ (formula_1323 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)) ∨ ((¬ (r3_kind = (0 : Int))) ∧ (formula_1330 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)))
abbrev formula_1331 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair047_58 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair047_59 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((formula_1309 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_1331 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
abbrev formula_1332 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair047_59 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

set_option maxHeartbeats 2000000 in
theorem normalized_1076 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15))) ∧ (¬ ((p47 ∧ (¬ p35)) ∧ (p15 ∧ (¬ p2)) ∧ (p52 ∧ (¬ p53))))) ∨ ((¬ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)))) ∧ ((((¬ p54) ∧ p55) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p56)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p56)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p59)))) ∨ (((¬ p60) ∧ p54) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p61) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p62)))))))))))) ↔ (((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15))) ∧ (¬ ((p47 ∧ (¬ p35)) ∧ (p15 ∧ (¬ p2)) ∧ (p52 ∧ (¬ p53))))) ∨ ((¬ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)))) ∧ ((((¬ p54) ∧ p55) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p56)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p56)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p59)))) ∨ (((¬ p60) ∧ p54) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p61) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p62))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4498 (c2_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ ((¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

abbrev shared_expr_Repair047_60 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
theorem normalization_4499 (c2_depth c2_kind c2_sign r3_level : Int) : ((c2_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (0 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (shared_expr_Repair047_60 c2_depth c2_kind c2_sign r3_level) := (and_congr (normalization_16 c2_kind) (and_congr (normalization_4498 c2_depth r3_level) (normalization_809 c2_sign)))

abbrev shared_expr_Repair047_61 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_60 c2_depth c2_kind c2_sign r3_level)))
theorem normalization_4500 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : (formula_1316 c2_depth c2_kind c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_61 c2_depth c2_kind c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_34 c2_kind)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_4499 c2_depth c2_kind c2_sign r3_level)))

theorem normalization_4501 (c2_depth c2_kind c2_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (0 : Int)) ∧ (formula_1316 c2_depth c2_kind c2_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_61 c2_depth c2_kind c2_sign r3_group r3_level)) := (and_congr (normalization_2656 r3_mode) (normalization_4500 c2_depth c2_kind c2_sign r3_group r3_level))

abbrev shared_expr_Repair047_62 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ∨ (((c2_sign) ≤ (2 : Int)) ∧ (¬ ((c2_sign) ≤ (1 : Int))))))
theorem normalization_4502 (c2_depth c2_kind c2_sign r3_level : Int) : ((c2_kind = (1 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ ((c2_sign = (1 : Int)) ∨ (c2_sign = (2 : Int)))) ↔ (shared_expr_Repair047_62 c2_depth c2_kind c2_sign r3_level) := (and_congr (normalization_16 c2_kind) (and_congr (normalization_4498 c2_depth r3_level) (normalization_813 c2_sign)))

abbrev shared_expr_Repair047_63 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_62 c2_depth c2_kind c2_sign r3_level)))
theorem normalization_4503 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : (formula_1317 c2_depth c2_kind c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_63 c2_depth c2_kind c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_34 c2_kind)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_4502 c2_depth c2_kind c2_sign r3_level)))

theorem normalization_4504 (c2_depth c2_kind c2_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (1 : Int)) ∧ (formula_1317 c2_depth c2_kind c2_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_63 c2_depth c2_kind c2_sign r3_group r3_level)) := (and_congr (normalization_4009 r3_mode) (normalization_4503 c2_depth c2_kind c2_sign r3_group r3_level))

abbrev shared_expr_Repair047_64 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_60 c2_depth c2_kind c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_5 c2_depth c2_kind c2_node c2_sign r3_level)))
theorem normalization_4505 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (formula_1318 c2_depth c2_kind c2_node c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_64 c2_depth c2_kind c2_node c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_4499 c2_depth c2_kind c2_sign r3_level)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_4440 c2_depth c2_kind c2_node c2_sign r3_level)))

theorem normalization_4506 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (2 : Int)) ∧ (formula_1318 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair047_64 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) := (and_congr (normalization_4013 r3_mode) (normalization_4505 c2_depth c2_kind c2_node c2_sign r3_group r3_level))

abbrev shared_expr_Repair047_65 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_60 c2_depth c2_kind c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_7 c2_depth c2_kind c2_node c2_sign r3_level)))
theorem normalization_4507 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (formula_1319 c2_depth c2_kind c2_node c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_65 c2_depth c2_kind c2_node c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_4499 c2_depth c2_kind c2_sign r3_level)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_4443 c2_depth c2_kind c2_node c2_sign r3_level)))

theorem normalization_4508 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (3 : Int)) ∧ (formula_1319 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair047_65 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) := (and_congr (normalization_4019 r3_mode) (normalization_4507 c2_depth c2_kind c2_node c2_sign r3_group r3_level))

abbrev shared_expr_Repair047_66 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_9 c2_depth c2_kind c2_node c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_62 c2_depth c2_kind c2_sign r3_level)))
theorem normalization_4509 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (formula_1320 c2_depth c2_kind c2_node c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_66 c2_depth c2_kind c2_node c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_4446 c2_depth c2_kind c2_node c2_sign r3_level)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_4502 c2_depth c2_kind c2_sign r3_level)))

theorem normalization_4510 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (4 : Int)) ∧ (formula_1320 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair047_66 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) := (and_congr (normalization_4023 r3_mode) (normalization_4509 c2_depth c2_kind c2_node c2_sign r3_group r3_level))

abbrev shared_expr_Repair047_67 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_11 c2_depth c2_kind c2_node c2_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair047_62 c2_depth c2_kind c2_sign r3_level)))
theorem normalization_4511 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (formula_1321 c2_depth c2_kind c2_node c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_67 c2_depth c2_kind c2_node c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2646 r3_group) (normalization_4449 c2_depth c2_kind c2_node c2_sign r3_level)) (and_congr (not_congr (normalization_2646 r3_group)) (normalization_4502 c2_depth c2_kind c2_sign r3_level)))

theorem normalization_4512 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((r3_mode = (5 : Int)) ∧ (formula_1321 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ↔ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair047_67 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) := (and_congr (normalization_4028 r3_mode) (normalization_4511 c2_depth c2_kind c2_node c2_sign r3_group r3_level))

abbrev shared_expr_Repair047_68 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_61 c2_depth c2_kind c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_63 c2_depth c2_kind c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair047_64 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair047_65 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair047_66 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair047_67 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))
theorem normalization_4513 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_1322 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_68 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) := (or_congr (normalization_4501 c2_depth c2_kind c2_sign r3_group r3_level r3_mode) (or_congr (normalization_4504 c2_depth c2_kind c2_sign r3_group r3_level r3_mode) (or_congr (normalization_4506 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (or_congr (normalization_4508 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (or_congr (normalization_4510 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (normalization_4512 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))))))

abbrev shared_expr_Repair047_69 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_0 c2_group c2_level c2_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair047_68 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))
theorem normalization_4514 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_1323 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_69 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_0 c2_kind) (normalization_4432 c2_group c2_level c2_mode r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_0 c2_kind)) (normalization_4513 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))

theorem normalization_4515 (c2_level r3_depth : Int) : ((r3_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ↔ ((¬ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_4516 (c2_level r3_depth r3_kind r3_sign : Int) : ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int)))) ↔ (shared_expr_Repair047_16 c2_level r3_depth r3_kind r3_sign) := (and_congr (normalization_1254 r3_kind) (and_congr (normalization_4515 c2_level r3_depth) (normalization_4035 r3_sign)))

theorem normalization_4517 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : (formula_1324 c2_group c2_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair047_17 c2_group c2_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_5 c2_group) (normalization_4386 c2_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_5 c2_group)) (normalization_4516 c2_level r3_depth r3_kind r3_sign)))

theorem normalization_4518 (c2_group c2_level c2_mode r3_depth r3_kind r3_sign : Int) : ((c2_mode = (0 : Int)) ∧ (formula_1324 c2_group c2_level r3_depth r3_kind r3_sign)) ↔ ((((c2_mode) ≤ (0 : Int)) ∧ (¬ ((c2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_17 c2_group c2_level r3_depth r3_kind r3_sign)) := (and_congr (normalization_17 c2_mode) (normalization_4517 c2_group c2_level r3_depth r3_kind r3_sign))

theorem normalization_4519 (c2_level r3_depth r3_kind r3_sign : Int) : ((r3_kind = (1 : Int)) ∧ ((r3_depth + ((-1 : Int) * c2_level)) = (-1 : Int)) ∧ ((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int)))) ↔ (shared_expr_Repair047_18 c2_level r3_depth r3_kind r3_sign) := (and_congr (normalization_1254 r3_kind) (and_congr (normalization_4515 c2_level r3_depth) (normalization_4041 r3_sign)))

theorem normalization_4520 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : (formula_1325 c2_group c2_level r3_depth r3_kind r3_sign) ↔ (shared_expr_Repair047_20 c2_group c2_level r3_depth r3_kind r3_sign) := (or_congr (and_congr (normalization_5 c2_group) (normalization_4519 c2_level r3_depth r3_kind r3_sign)) (and_congr (not_congr (normalization_5 c2_group)) (normalization_4392 c2_level r3_depth r3_kind r3_sign)))

theorem normalization_4521 (c2_group c2_level c2_mode r3_depth r3_kind r3_sign : Int) : ((c2_mode = (1 : Int)) ∧ (formula_1325 c2_group c2_level r3_depth r3_kind r3_sign)) ↔ ((((c2_mode) ≤ (1 : Int)) ∧ (¬ ((c2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair047_20 c2_group c2_level r3_depth r3_kind r3_sign)) := (and_congr (normalization_842 c2_mode) (normalization_4520 c2_group c2_level r3_depth r3_kind r3_sign))

theorem normalization_4522 (c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign : Int) : (formula_1326 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair047_29 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) := (or_congr (normalization_4518 c2_group c2_level c2_mode r3_depth r3_kind r3_sign) (or_congr (normalization_4521 c2_group c2_level c2_mode r3_depth r3_kind r3_sign) (or_congr (normalization_4463 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_4466 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) (or_congr (normalization_4469 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign) (normalization_4472 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign))))))

theorem normalization_4523 (c2_node r3_node : Int) : ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4524 (c2_node c2_sign r3_node r3_sign : Int) : ((r3_sign = (0 : Int)) ∧ (c2_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_1259 r3_sign) (and_congr (normalization_10 c2_sign) (normalization_4523 c2_node r3_node)))

theorem normalization_4525 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((r3_sign = (2 : Int)) ∧ (c2_sign = (2 : Int)) ∧ (r3_depth = h) ∧ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (shared_expr_Repair047_31 c2_node c2_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2664 r3_sign) (and_congr (normalization_25 c2_sign) (and_congr (normalization_2663 h r3_depth) (normalization_4523 c2_node r3_node))))

theorem normalization_4526 (c2_node r3_node : Int) : ((r3_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4527 (c2_node r3_node : Int) : (¬ ((r3_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) := (not_congr (normalization_4526 c2_node r3_node))

theorem normalization_4528 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((r3_sign = (1 : Int)) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair047_32 c2_node c2_sign h r3_depth r3_node r3_sign) := (and_congr (normalization_2665 r3_sign) (and_congr (normalization_26 c2_sign) (and_congr (normalization_2736 h r3_depth) (normalization_4527 c2_node r3_node))))

theorem normalization_4529 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (formula_1327 c2_node c2_sign h r3_depth r3_node r3_sign) ↔ (shared_expr_Repair047_33 c2_node c2_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_4524 c2_node c2_sign r3_node r3_sign) (or_congr (normalization_4525 c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_4528 c2_node c2_sign h r3_depth r3_node r3_sign)))

theorem normalization_4530 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((r3_depth = c2_depth) ∧ (formula_1327 c2_node c2_sign h r3_depth r3_node r3_sign)) ↔ (((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair047_33 c2_node c2_sign h r3_depth r3_node r3_sign)) := (and_congr (normalization_4411 c2_depth r3_depth) (normalization_4529 c2_node c2_sign h r3_depth r3_node r3_sign))

theorem normalization_4531 (c2_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ ((¬ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int))) ∧ ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4532 (c2_node r3_node : Int) : ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4533 (c2_node c2_sign r3_node r3_sign : Int) : (((r3_sign = (0 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c2_sign = (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (shared_expr_Repair047_34 c2_node c2_sign r3_node r3_sign) := (and_congr (normalization_4035 r3_sign) (and_congr (normalization_10 c2_sign) (normalization_4532 c2_node r3_node)))

theorem normalization_4534 (c2_node r3_node : Int) : ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4535 (c2_node r3_node : Int) : (¬ ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4534 c2_node r3_node))

theorem normalization_4536 (c2_node c2_sign r3_node r3_sign : Int) : (((r3_sign = (1 : Int)) ∨ (r3_sign = (2 : Int))) ∧ (c2_sign = (1 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))) ↔ (shared_expr_Repair047_35 c2_node c2_sign r3_node r3_sign) := (and_congr (normalization_4041 r3_sign) (and_congr (normalization_26 c2_sign) (normalization_4535 c2_node r3_node)))

theorem normalization_4537 (c2_node c2_sign r3_node r3_sign : Int) : (formula_1328 c2_node c2_sign r3_node r3_sign) ↔ ((shared_expr_Repair047_34 c2_node c2_sign r3_node r3_sign) ∨ (shared_expr_Repair047_35 c2_node c2_sign r3_node r3_sign)) := (or_congr (normalization_4533 c2_node c2_sign r3_node r3_sign) (normalization_4536 c2_node c2_sign r3_node r3_sign))

theorem normalization_4538 (c2_depth c2_node c2_sign r3_depth r3_node r3_sign : Int) : (((r3_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1328 c2_node c2_sign r3_node r3_sign)) ↔ (shared_expr_Repair047_36 c2_depth c2_node c2_sign r3_depth r3_node r3_sign) := (and_congr (normalization_4531 c2_depth r3_depth) (normalization_4537 c2_node c2_sign r3_node r3_sign))

theorem normalization_4539 (c2_depth c2_node c2_sign h r3_depth r3_node r3_sign : Int) : (((r3_depth = c2_depth) ∧ (formula_1327 c2_node c2_sign h r3_depth r3_node r3_sign)) ∨ (((r3_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ∧ (formula_1328 c2_node c2_sign r3_node r3_sign))) ↔ (shared_expr_Repair047_37 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) := (or_congr (normalization_4530 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (normalization_4538 c2_depth c2_node c2_sign r3_depth r3_node r3_sign))

theorem normalization_4540 (c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1329 c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair047_39 c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_4408 c2_kind r3_kind) (normalization_4410 c2_depth c2_kind h r3_kind)) (and_congr (not_congr (normalization_4408 c2_kind r3_kind)) (normalization_4539 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign)))

theorem normalization_4541 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_1330 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign) ↔ (shared_expr_Repair047_40 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign) := (or_congr (and_congr (normalization_0 c2_kind) (normalization_4522 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) (and_congr (not_congr (normalization_0 c2_kind)) (normalization_4540 c2_depth c2_kind c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Repair047_70 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair047_69 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)) ∨ ((¬ (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair047_40 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)))
theorem normalization_4542 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1331 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair047_70 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (or_congr (and_congr (normalization_1241 r3_kind) (normalization_4514 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_1241 r3_kind)) (normalization_4541 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_kind r3_node r3_sign)))

abbrev shared_expr_Repair047_71 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((shared_expr_Repair047_41 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair047_70 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))
theorem normalization_4543 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1332 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair047_71 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (iff_congr (normalization_4488 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_4542 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_2693 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_1332 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  classical
  have ht := (normalized_1076 ((r3_kind) ≤ (0 : Int)) ((r3_kind) ≤ (-1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_kind) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ((r3_mode) ≤ (0 : Int)) ((r3_mode) ≤ (-1 : Int)) ((r3_group) ≤ (1 : Int)) ((r3_group) ≤ (0 : Int)) ((c2_kind) ≤ (2 : Int)) ((c2_kind) ≤ (1 : Int)) ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)) ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) ((c2_sign) ≤ (2 : Int)) ((c2_sign) ≤ (1 : Int)) ((r3_mode) ≤ (1 : Int)) ((r3_mode) ≤ (2 : Int)) ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((r3_mode) ≤ (3 : Int)) ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-2 : Int)) ((r3_mode) ≤ (4 : Int)) ((r3_mode) ≤ (5 : Int)) ((c2_mode) ≤ (0 : Int)) ((c2_mode) ≤ (-1 : Int)) ((c2_group) ≤ (1 : Int)) ((c2_group) ≤ (0 : Int)) ((r3_kind) ≤ (1 : Int)) ((c2_level + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((r3_sign) ≤ (2 : Int)) ((r3_sign) ≤ (1 : Int)) ((c2_level + ((-1 : Int) * r3_depth)) ≤ (1 : Int)) ((c2_mode) ≤ (1 : Int)) ((c2_mode) ≤ (2 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-1 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ((r3_kind) ≤ (2 : Int)) ((c2_mode) ≤ (3 : Int)) ((((2 : Int) * (r3_node / (2 : Int))) + ((-1 : Int) * r3_node)) ≤ (-2 : Int)) ((c2_mode) ≤ (4 : Int)) ((c2_mode) ≤ (5 : Int)) ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * r3_depth)) ≤ (-2 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) (((r3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4543 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

-- Checked replay of mp.
theorem replay_2694 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i178 : ((formula_1289 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_1331 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_2693 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_2692 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i178)

theorem normalized_1077 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4544 (c2_mode r3_mode : Int) : (r3_mode ≤ c2_mode) ↔ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4545 (c2_mode r3_mode : Int) : (r3_mode ≥ c2_mode) ↔ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_4546 (c2_mode r3_mode : Int) : ((r3_mode ≤ c2_mode) ∧ (r3_mode ≥ c2_mode)) ↔ ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_4544 c2_mode r3_mode) (normalization_4545 c2_mode r3_mode))

abbrev shared_expr_Repair047_72 (c2_mode r3_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
theorem normalization_4547 (c2_mode r3_mode : Int) : ((r3_mode = c2_mode) ↔ ((r3_mode ≤ c2_mode) ∧ (r3_mode ≥ c2_mode))) ↔ (shared_expr_Repair047_72 c2_mode r3_mode) := (iff_congr (normalization_4357 c2_mode r3_mode) (normalization_4546 c2_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_2695 (c2_mode r3_mode : Int) : ((r3_mode = c2_mode) ↔ ((r3_mode ≤ c2_mode) ∧ (r3_mode ≥ c2_mode))) := by
  classical
  have ht := (normalized_1077 ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4547 c2_mode r3_mode) hn

theorem normalized_1078 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4548 (c2_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ↔ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4549 (c2_mode r3_mode : Int) : ((r3_mode ≤ c2_mode) ↔ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_4544 c2_mode r3_mode) (normalization_4548 c2_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_2696 (c2_mode r3_mode : Int) : ((r3_mode ≤ c2_mode) ↔ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1078 ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4549 c2_mode r3_mode) hn

theorem normalized_1079 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4550 (c2_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_4551 (c2_mode r3_mode : Int) : ((r3_mode ≥ c2_mode) ↔ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (iff_congr (normalization_4545 c2_mode r3_mode) (normalization_4550 c2_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_2697 (c2_mode r3_mode : Int) : ((r3_mode ≥ c2_mode) ↔ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1079 ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4551 c2_mode r3_mode) hn

theorem normalized_1080 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4552 (c2_mode r3_mode : Int) : (((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_4548 c2_mode r3_mode) (normalization_4550 c2_mode r3_mode))

theorem normalization_4553 (c2_mode r3_mode : Int) : (((r3_mode ≤ c2_mode) ∧ (r3_mode ≥ c2_mode)) ↔ (((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Repair047_72 c2_mode r3_mode) := (iff_congr (normalization_4546 c2_mode r3_mode) (normalization_4552 c2_mode r3_mode))

-- Checked replay of monotonicity.
theorem replay_2698 (c2_mode r3_mode : Int) : (((r3_mode ≤ c2_mode) ∧ (r3_mode ≥ c2_mode)) ↔ (((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1080 ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4549 c2_mode r3_mode) (replay_2696 c2_mode r3_mode)
  have n1 : (((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4551 c2_mode r3_mode) (replay_2697 c2_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4553 c2_mode r3_mode) hn

abbrev shared_expr_Repair047_73 (c2_mode r3_mode : Int) : Prop := ((((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))))
abbrev formula_1333 (c2_mode r3_mode : Int) : Prop := (shared_expr_Repair047_73 c2_mode r3_mode)

theorem normalized_1081 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4554 (c2_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_4548 c2_mode r3_mode))

theorem normalization_4555 (c2_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (not_congr (normalization_4550 c2_mode r3_mode))

theorem normalization_4556 (c2_mode r3_mode : Int) : ((¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) := (or_congr (normalization_4554 c2_mode r3_mode) (normalization_4555 c2_mode r3_mode))

theorem normalization_4557 (c2_mode r3_mode : Int) : (¬ ((¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) := (not_congr (normalization_4556 c2_mode r3_mode))

abbrev shared_expr_Repair047_74 (c2_mode r3_mode : Int) : Prop := (((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))))
theorem normalization_4558 (c2_mode r3_mode : Int) : (formula_1333 c2_mode r3_mode) ↔ (shared_expr_Repair047_74 c2_mode r3_mode) := (iff_congr (normalization_4552 c2_mode r3_mode) (normalization_4557 c2_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_2699 (c2_mode r3_mode : Int) : (formula_1333 c2_mode r3_mode) := by
  classical
  have ht := (normalized_1081 ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4558 c2_mode r3_mode) hn

theorem normalized_1082 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4559 (c2_mode r3_mode : Int) : (((r3_mode ≤ c2_mode) ∧ (r3_mode ≥ c2_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair047_74 c2_mode r3_mode) := (iff_congr (normalization_4546 c2_mode r3_mode) (normalization_4557 c2_mode r3_mode))

-- Checked replay of trans.
theorem replay_2700 (c2_mode r3_mode : Int) : (((r3_mode ≤ c2_mode) ∧ (r3_mode ≥ c2_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1082 ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Repair047_74 c2_mode r3_mode))
  have n0 : (shared_expr_Repair047_72 c2_mode r3_mode) := by
    exact Iff.mp (normalization_4553 c2_mode r3_mode) (replay_2698 c2_mode r3_mode)
  have n1 : (shared_expr_Repair047_74 c2_mode r3_mode) := by
    exact Iff.mp (normalization_4558 c2_mode r3_mode) (replay_2699 c2_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4559 c2_mode r3_mode) hn

theorem normalized_1083 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4560 (c2_mode r3_mode : Int) : ((r3_mode = c2_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair047_74 c2_mode r3_mode) := (iff_congr (normalization_4357 c2_mode r3_mode) (normalization_4557 c2_mode r3_mode))

-- Checked replay of trans.
theorem replay_2701 (c2_mode r3_mode : Int) : ((r3_mode = c2_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1083 ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Repair047_74 c2_mode r3_mode))
  have n0 : (shared_expr_Repair047_72 c2_mode r3_mode) := by
    exact Iff.mp (normalization_4547 c2_mode r3_mode) (replay_2695 c2_mode r3_mode)
  have n1 : (shared_expr_Repair047_74 c2_mode r3_mode) := by
    exact Iff.mp (normalization_4559 c2_mode r3_mode) (replay_2700 c2_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4560 c2_mode r3_mode) hn

theorem normalized_1084 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4561 (c2_level r3_level : Int) : (r3_level ≤ c2_level) ↔ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4562 (c2_level r3_level : Int) : (r3_level ≥ c2_level) ↔ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4563 (c2_level r3_level : Int) : ((r3_level ≤ c2_level) ∧ (r3_level ≥ c2_level)) ↔ ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_4561 c2_level r3_level) (normalization_4562 c2_level r3_level))

abbrev shared_expr_Repair047_75 (c2_level r3_level : Int) : Prop := (((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
theorem normalization_4564 (c2_level r3_level : Int) : ((r3_level = c2_level) ↔ ((r3_level ≤ c2_level) ∧ (r3_level ≥ c2_level))) ↔ (shared_expr_Repair047_75 c2_level r3_level) := (iff_congr (normalization_4358 c2_level r3_level) (normalization_4563 c2_level r3_level))

-- Checked replay of rewrite.
theorem replay_2702 (c2_level r3_level : Int) : ((r3_level = c2_level) ↔ ((r3_level ≤ c2_level) ∧ (r3_level ≥ c2_level))) := by
  classical
  have ht := (normalized_1084 ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4564 c2_level r3_level) hn

theorem normalized_1085 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4565 (c2_level r3_level : Int) : ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ↔ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4566 (c2_level r3_level : Int) : ((r3_level ≤ c2_level) ↔ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_4561 c2_level r3_level) (normalization_4565 c2_level r3_level))

-- Checked replay of rewrite.
theorem replay_2703 (c2_level r3_level : Int) : ((r3_level ≤ c2_level) ↔ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1085 ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4566 c2_level r3_level) hn

theorem normalized_1086 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4567 (c2_level r3_level : Int) : ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4568 (c2_level r3_level : Int) : ((r3_level ≥ c2_level) ↔ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (iff_congr (normalization_4562 c2_level r3_level) (normalization_4567 c2_level r3_level))

-- Checked replay of rewrite.
theorem replay_2704 (c2_level r3_level : Int) : ((r3_level ≥ c2_level) ↔ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1086 ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4568 c2_level r3_level) hn

theorem normalized_1087 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4569 (c2_level r3_level : Int) : (((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_4565 c2_level r3_level) (normalization_4567 c2_level r3_level))

theorem normalization_4570 (c2_level r3_level : Int) : (((r3_level ≤ c2_level) ∧ (r3_level ≥ c2_level)) ↔ (((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ (shared_expr_Repair047_75 c2_level r3_level) := (iff_congr (normalization_4563 c2_level r3_level) (normalization_4569 c2_level r3_level))

-- Checked replay of monotonicity.
theorem replay_2705 (c2_level r3_level : Int) : (((r3_level ≤ c2_level) ∧ (r3_level ≥ c2_level)) ↔ (((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1087 ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4566 c2_level r3_level) (replay_2703 c2_level r3_level)
  have n1 : (((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4568 c2_level r3_level) (replay_2704 c2_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4570 c2_level r3_level) hn

abbrev shared_expr_Repair047_76 (c2_level r3_level : Int) : Prop := ((((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))))
abbrev formula_1334 (c2_level r3_level : Int) : Prop := (shared_expr_Repair047_76 c2_level r3_level)

theorem normalized_1088 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4571 (c2_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4565 c2_level r3_level))

theorem normalization_4572 (c2_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_4567 c2_level r3_level))

theorem normalization_4573 (c2_level r3_level : Int) : ((¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) := (or_congr (normalization_4571 c2_level r3_level) (normalization_4572 c2_level r3_level))

theorem normalization_4574 (c2_level r3_level : Int) : (¬ ((¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) := (not_congr (normalization_4573 c2_level r3_level))

abbrev shared_expr_Repair047_77 (c2_level r3_level : Int) : Prop := (((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))))
theorem normalization_4575 (c2_level r3_level : Int) : (formula_1334 c2_level r3_level) ↔ (shared_expr_Repair047_77 c2_level r3_level) := (iff_congr (normalization_4569 c2_level r3_level) (normalization_4574 c2_level r3_level))

-- Checked replay of rewrite.
theorem replay_2706 (c2_level r3_level : Int) : (formula_1334 c2_level r3_level) := by
  classical
  have ht := (normalized_1088 ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4575 c2_level r3_level) hn

theorem normalized_1089 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4576 (c2_level r3_level : Int) : (((r3_level ≤ c2_level) ∧ (r3_level ≥ c2_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair047_77 c2_level r3_level) := (iff_congr (normalization_4563 c2_level r3_level) (normalization_4574 c2_level r3_level))

-- Checked replay of trans.
theorem replay_2707 (c2_level r3_level : Int) : (((r3_level ≤ c2_level) ∧ (r3_level ≥ c2_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1089 ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Repair047_77 c2_level r3_level))
  have n0 : (shared_expr_Repair047_75 c2_level r3_level) := by
    exact Iff.mp (normalization_4570 c2_level r3_level) (replay_2705 c2_level r3_level)
  have n1 : (shared_expr_Repair047_77 c2_level r3_level) := by
    exact Iff.mp (normalization_4575 c2_level r3_level) (replay_2706 c2_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4576 c2_level r3_level) hn

theorem normalized_1090 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4577 (c2_level r3_level : Int) : ((r3_level = c2_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair047_77 c2_level r3_level) := (iff_congr (normalization_4358 c2_level r3_level) (normalization_4574 c2_level r3_level))

-- Checked replay of trans.
theorem replay_2708 (c2_level r3_level : Int) : ((r3_level = c2_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1090 ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Repair047_77 c2_level r3_level))
  have n0 : (shared_expr_Repair047_75 c2_level r3_level) := by
    exact Iff.mp (normalization_4564 c2_level r3_level) (replay_2702 c2_level r3_level)
  have n1 : (shared_expr_Repair047_77 c2_level r3_level) := by
    exact Iff.mp (normalization_4576 c2_level r3_level) (replay_2707 c2_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4577 c2_level r3_level) hn

theorem normalized_1091 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4578 (c2_group r3_group : Int) : (r3_group ≤ c2_group) ↔ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4579 (c2_group r3_group : Int) : (r3_group ≥ c2_group) ↔ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_4580 (c2_group r3_group : Int) : ((r3_group ≤ c2_group) ∧ (r3_group ≥ c2_group)) ↔ ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_4578 c2_group r3_group) (normalization_4579 c2_group r3_group))

abbrev shared_expr_Repair047_78 (c2_group r3_group : Int) : Prop := (((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
theorem normalization_4581 (c2_group r3_group : Int) : ((r3_group = c2_group) ↔ ((r3_group ≤ c2_group) ∧ (r3_group ≥ c2_group))) ↔ (shared_expr_Repair047_78 c2_group r3_group) := (iff_congr (normalization_4430 c2_group r3_group) (normalization_4580 c2_group r3_group))

-- Checked replay of rewrite.
theorem replay_2709 (c2_group r3_group : Int) : ((r3_group = c2_group) ↔ ((r3_group ≤ c2_group) ∧ (r3_group ≥ c2_group))) := by
  classical
  have ht := (normalized_1091 ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_4581 c2_group r3_group) hn

theorem normalized_1092 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4582 (c2_group r3_group : Int) : ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ↔ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4583 (c2_group r3_group : Int) : ((r3_group ≤ c2_group) ↔ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_4578 c2_group r3_group) (normalization_4582 c2_group r3_group))

-- Checked replay of rewrite.
theorem replay_2710 (c2_group r3_group : Int) : ((r3_group ≤ c2_group) ↔ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1092 ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4583 c2_group r3_group) hn

theorem normalized_1093 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4584 (c2_group r3_group : Int) : ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_4585 (c2_group r3_group : Int) : ((r3_group ≥ c2_group) ↔ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (iff_congr (normalization_4579 c2_group r3_group) (normalization_4584 c2_group r3_group))

-- Checked replay of rewrite.
theorem replay_2711 (c2_group r3_group : Int) : ((r3_group ≥ c2_group) ↔ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1093 ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4585 c2_group r3_group) hn

theorem normalized_1094 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4586 (c2_group r3_group : Int) : (((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_4582 c2_group r3_group) (normalization_4584 c2_group r3_group))

theorem normalization_4587 (c2_group r3_group : Int) : (((r3_group ≤ c2_group) ∧ (r3_group ≥ c2_group)) ↔ (((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ↔ (shared_expr_Repair047_78 c2_group r3_group) := (iff_congr (normalization_4580 c2_group r3_group) (normalization_4586 c2_group r3_group))

-- Checked replay of monotonicity.
theorem replay_2712 (c2_group r3_group : Int) : (((r3_group ≤ c2_group) ∧ (r3_group ≥ c2_group)) ↔ (((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1094 ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4583 c2_group r3_group) (replay_2710 c2_group r3_group)
  have n1 : (((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4585 c2_group r3_group) (replay_2711 c2_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4587 c2_group r3_group) hn

abbrev shared_expr_Repair047_79 (c2_group r3_group : Int) : Prop := ((((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))
abbrev formula_1335 (c2_group r3_group : Int) : Prop := (shared_expr_Repair047_79 c2_group r3_group)

theorem normalized_1095 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4588 (c2_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_4582 c2_group r3_group))

theorem normalization_4589 (c2_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (not_congr (normalization_4584 c2_group r3_group))

theorem normalization_4590 (c2_group r3_group : Int) : ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) := (or_congr (normalization_4588 c2_group r3_group) (normalization_4589 c2_group r3_group))

theorem normalization_4591 (c2_group r3_group : Int) : (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))) := (not_congr (normalization_4590 c2_group r3_group))

abbrev shared_expr_Repair047_80 (c2_group r3_group : Int) : Prop := (((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_4592 (c2_group r3_group : Int) : (formula_1335 c2_group r3_group) ↔ (shared_expr_Repair047_80 c2_group r3_group) := (iff_congr (normalization_4586 c2_group r3_group) (normalization_4591 c2_group r3_group))

-- Checked replay of rewrite.
theorem replay_2713 (c2_group r3_group : Int) : (formula_1335 c2_group r3_group) := by
  classical
  have ht := (normalized_1095 ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4592 c2_group r3_group) hn

theorem normalized_1096 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4593 (c2_group r3_group : Int) : (((r3_group ≤ c2_group) ∧ (r3_group ≥ c2_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair047_80 c2_group r3_group) := (iff_congr (normalization_4580 c2_group r3_group) (normalization_4591 c2_group r3_group))

-- Checked replay of trans.
theorem replay_2714 (c2_group r3_group : Int) : (((r3_group ≤ c2_group) ∧ (r3_group ≥ c2_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1096 ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Repair047_80 c2_group r3_group))
  have n0 : (shared_expr_Repair047_78 c2_group r3_group) := by
    exact Iff.mp (normalization_4587 c2_group r3_group) (replay_2712 c2_group r3_group)
  have n1 : (shared_expr_Repair047_80 c2_group r3_group) := by
    exact Iff.mp (normalization_4592 c2_group r3_group) (replay_2713 c2_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4593 c2_group r3_group) hn

theorem normalized_1097 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4594 (c2_group r3_group : Int) : ((r3_group = c2_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair047_80 c2_group r3_group) := (iff_congr (normalization_4430 c2_group r3_group) (normalization_4591 c2_group r3_group))

-- Checked replay of trans.
theorem replay_2715 (c2_group r3_group : Int) : ((r3_group = c2_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1097 ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Repair047_80 c2_group r3_group))
  have n0 : (shared_expr_Repair047_78 c2_group r3_group) := by
    exact Iff.mp (normalization_4581 c2_group r3_group) (replay_2709 c2_group r3_group)
  have n1 : (shared_expr_Repair047_80 c2_group r3_group) := by
    exact Iff.mp (normalization_4593 c2_group r3_group) (replay_2714 c2_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4594 c2_group r3_group) hn

theorem normalized_1098 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4595 (c2_group r3_group : Int) : (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) := (not_congr (normalization_4591 c2_group r3_group))

abbrev shared_expr_Repair047_81 (c2_group r3_group : Int) : Prop := ((¬ ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))))
theorem normalization_4596 (c2_group r3_group : Int) : ((¬ (r3_group = c2_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Repair047_81 c2_group r3_group) := (iff_congr (normalization_4431 c2_group r3_group) (normalization_4595 c2_group r3_group))

-- Checked replay of monotonicity.
theorem replay_2716 (c2_group r3_group : Int) : ((¬ (r3_group = c2_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1098 ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair047_80 c2_group r3_group) := by
    exact Iff.mp (normalization_4594 c2_group r3_group) (replay_2715 c2_group r3_group)
  have hn := ht n0
  exact Iff.mpr (normalization_4596 c2_group r3_group) hn

abbrev shared_expr_Repair047_82 (c2_group r3_group : Int) : Prop := ((¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))
abbrev formula_1336 (c2_group r3_group : Int) : Prop := (shared_expr_Repair047_82 c2_group r3_group)

theorem normalized_1099 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair047_83 (c2_group r3_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_4597 (c2_group r3_group : Int) : (formula_1336 c2_group r3_group) ↔ (shared_expr_Repair047_83 c2_group r3_group) := (iff_congr (normalization_4595 c2_group r3_group) (normalization_4590 c2_group r3_group))

-- Checked replay of rewrite.
theorem replay_2717 (c2_group r3_group : Int) : (formula_1336 c2_group r3_group) := by
  classical
  have ht := (normalized_1099 ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4597 c2_group r3_group) hn

theorem normalized_1100 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair047_84 (c2_group r3_group : Int) : Prop := ((¬ ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_4598 (c2_group r3_group : Int) : ((¬ (r3_group = c2_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) ↔ (shared_expr_Repair047_84 c2_group r3_group) := (iff_congr (normalization_4431 c2_group r3_group) (normalization_4590 c2_group r3_group))

-- Checked replay of trans.
theorem replay_2718 (c2_group r3_group : Int) : ((¬ (r3_group = c2_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1100 ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair047_81 c2_group r3_group) := by
    exact Iff.mp (normalization_4596 c2_group r3_group) (replay_2716 c2_group r3_group)
  have n1 : (shared_expr_Repair047_83 c2_group r3_group) := by
    exact Iff.mp (normalization_4597 c2_group r3_group) (replay_2717 c2_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4598 c2_group r3_group) hn

abbrev shared_expr_Repair047_85 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r3_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))) ∧ ((¬ ((r3_group + ((-1 : Int) * c2_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))
abbrev formula_1337 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair047_85 c2_group c2_level c2_mode r3_group r3_level r3_mode)

theorem normalized_1101 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair047_86 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_4599 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : (formula_1337 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_86 c2_group c2_level c2_mode r3_group r3_level r3_mode) := (and_congr (normalization_4557 c2_mode r3_mode) (and_congr (normalization_4574 c2_level r3_level) (normalization_4590 c2_group r3_group)))

theorem normalization_4600 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c2_mode) ∧ (r3_level = c2_level) ∧ (¬ (r3_group = c2_group))) ↔ (formula_1337 c2_group c2_level c2_mode r3_group r3_level r3_mode)) ↔ ((shared_expr_Repair047_0 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_86 c2_group c2_level c2_mode r3_group r3_level r3_mode)) := (iff_congr (normalization_4432 c2_group c2_level c2_mode r3_group r3_level r3_mode) (normalization_4599 c2_group c2_level c2_mode r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_2719 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c2_mode) ∧ (r3_level = c2_level) ∧ (¬ (r3_group = c2_group))) ↔ (formula_1337 c2_group c2_level c2_mode r3_group r3_level r3_mode)) := by
  classical
  have ht := (normalized_1101 ((¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ((¬ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) ((¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ((¬ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) ((¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Repair047_74 c2_mode r3_mode) := by
    exact Iff.mp (normalization_4560 c2_mode r3_mode) (replay_2701 c2_mode r3_mode)
  have n1 : (shared_expr_Repair047_77 c2_level r3_level) := by
    exact Iff.mp (normalization_4577 c2_level r3_level) (replay_2708 c2_level r3_level)
  have n2 : (shared_expr_Repair047_84 c2_group r3_group) := by
    exact Iff.mp (normalization_4598 c2_group r3_group) (replay_2718 c2_group r3_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4600 c2_group c2_level c2_mode r3_group r3_level r3_mode) hn

theorem normalized_1102 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair047_87 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_4601 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : (formula_1266 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode) := (or_congr (normalization_4554 c2_mode r3_mode) (or_congr (normalization_4555 c2_mode r3_mode) (or_congr (normalization_4571 c2_level r3_level) (or_congr (normalization_4572 c2_level r3_level) (normalization_4591 c2_group r3_group)))))

theorem normalization_4602 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : (¬ (formula_1266 c2_group c2_level c2_mode r3_group r3_level r3_mode)) ↔ (¬ (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode)) := (not_congr (normalization_4601 c2_group c2_level c2_mode r3_group r3_level r3_mode))

theorem normalization_4603 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : ((formula_1337 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (¬ (formula_1266 c2_group c2_level c2_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Repair047_86 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_4599 c2_group c2_level c2_mode r3_group r3_level r3_mode) (normalization_4602 c2_group c2_level c2_mode r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_2720 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : ((formula_1337 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (¬ (formula_1266 c2_group c2_level c2_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_1102 ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c2_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c2_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4603 c2_group c2_level c2_mode r3_group r3_level r3_mode) hn

theorem normalized_1103 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4604 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c2_mode) ∧ (r3_level = c2_level) ∧ (¬ (r3_group = c2_group))) ↔ (¬ (formula_1266 c2_group c2_level c2_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Repair047_0 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_4432 c2_group c2_level c2_mode r3_group r3_level r3_mode) (normalization_4602 c2_group c2_level c2_mode r3_group r3_level r3_mode))

-- Checked replay of trans.
theorem replay_2721 (c2_group c2_level c2_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c2_mode) ∧ (r3_level = c2_level) ∧ (¬ (r3_group = c2_group))) ↔ (¬ (formula_1266 c2_group c2_level c2_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_1103 (shared_expr_Repair047_0 c2_group c2_level c2_mode r3_group r3_level r3_mode) (shared_expr_Repair047_86 c2_group c2_level c2_mode r3_group r3_level r3_mode) (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode))
  have n0 : ((shared_expr_Repair047_0 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_86 c2_group c2_level c2_mode r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_4600 c2_group c2_level c2_mode r3_group r3_level r3_mode) (replay_2719 c2_group c2_level c2_mode r3_group r3_level r3_mode)
  have n1 : ((shared_expr_Repair047_86 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_4603 c2_group c2_level c2_mode r3_group r3_level r3_mode) (replay_2720 c2_group c2_level c2_mode r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4604 c2_group c2_level c2_mode r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_2722 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((formula_1322 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) ↔ (formula_1265 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)) := by
  classical
  first
  | (simp only [formula_1322, shared_expr_Repair047_48, formula_1316, shared_expr_Repair047_42, formula_1317, shared_expr_Repair047_43, formula_1318, shared_expr_Repair047_44, formula_1319, shared_expr_Repair047_45, formula_1320, shared_expr_Repair047_46, formula_1321, shared_expr_Repair047_47, formula_1265, shared_expr_Repair046_59, formula_1254, shared_expr_Repair046_48, formula_1253, shared_expr_Repair046_47, formula_1256, shared_expr_Repair046_50, formula_1255, shared_expr_Repair046_49, formula_1258, shared_expr_Repair046_52, formula_1257, shared_expr_Repair046_51, formula_1260, shared_expr_Repair046_54, formula_1259, shared_expr_Repair046_53, formula_1262, shared_expr_Repair046_56, formula_1261, shared_expr_Repair046_55, formula_1264, shared_expr_Repair046_58, formula_1263, shared_expr_Repair046_57, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Repair047_88 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∧ (¬ (formula_1266 c2_group c2_level c2_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) ∧ (formula_1265 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))
abbrev formula_1338 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair047_88 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)

abbrev shared_expr_Repair047_89 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_1323 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (formula_1338 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))
abbrev formula_1339 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Repair047_89 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode)

theorem normalized_1104 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4605 (c2_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_4606 (c2_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) := (not_congr (normalization_4605 c2_depth r3_level))

theorem normalization_4607 (c2_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ↔ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_4608 (c2_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := (not_congr (normalization_4607 c2_depth r3_level))

abbrev shared_expr_Repair047_90 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_4609 (c2_depth c2_kind c2_sign r3_level : Int) : (formula_1253 c2_depth c2_kind c2_sign r3_level) ↔ (shared_expr_Repair047_90 c2_depth c2_kind c2_sign r3_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1068 c2_sign) (or_congr (normalization_4606 c2_depth r3_level) (normalization_4608 c2_depth r3_level)))))

theorem normalization_4610 (c2_depth c2_kind c2_sign r3_level : Int) : (¬ (formula_1253 c2_depth c2_kind c2_sign r3_level)) ↔ (¬ (shared_expr_Repair047_90 c2_depth c2_kind c2_sign r3_level)) := (not_congr (normalization_4609 c2_depth c2_kind c2_sign r3_level))

abbrev shared_expr_Repair047_91 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair047_90 c2_depth c2_kind c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
theorem normalization_4611 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : (formula_1254 c2_depth c2_kind c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_91 c2_depth c2_kind c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_4610 c2_depth c2_kind c2_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_1076 c2_kind)))

theorem normalization_4612 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : (¬ (formula_1254 c2_depth c2_kind c2_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair047_91 c2_depth c2_kind c2_sign r3_group r3_level)) := (not_congr (normalization_4611 c2_depth c2_kind c2_sign r3_group r3_level))

theorem normalization_4613 (c2_depth c2_kind c2_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_1254 c2_depth c2_kind c2_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair047_91 c2_depth c2_kind c2_sign r3_group r3_level))) := (or_congr (normalization_2690 r3_mode) (or_congr (normalization_2691 r3_mode) (normalization_4612 c2_depth c2_kind c2_sign r3_group r3_level)))

theorem normalization_4614 (c2_depth c2_kind c2_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_1254 c2_depth c2_kind c2_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair047_91 c2_depth c2_kind c2_sign r3_group r3_level)))) := (not_congr (normalization_4613 c2_depth c2_kind c2_sign r3_group r3_level r3_mode))

theorem normalization_4615 (r3_mode : Int) : (r3_mode ≤ (1 : Int)) ↔ ((r3_mode) ≤ (1 : Int)) := by
  omega

theorem normalization_4616 (r3_mode : Int) : (¬ (r3_mode ≤ (1 : Int))) ↔ (¬ ((r3_mode) ≤ (1 : Int))) := (not_congr (normalization_4615 r3_mode))

theorem normalization_4617 (r3_mode : Int) : (r3_mode ≥ (1 : Int)) ↔ (¬ ((r3_mode) ≤ (0 : Int))) := by
  omega

theorem normalization_4618 (r3_mode : Int) : (¬ (r3_mode ≥ (1 : Int))) ↔ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) := (not_congr (normalization_4617 r3_mode))

abbrev shared_expr_Repair047_92 (c2_depth c2_kind c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_4619 (c2_depth c2_kind c2_sign r3_level : Int) : (formula_1255 c2_depth c2_kind c2_sign r3_level) ↔ (shared_expr_Repair047_92 c2_depth c2_kind c2_sign r3_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1082 c2_sign) (or_congr (normalization_4606 c2_depth r3_level) (normalization_4608 c2_depth r3_level)))))

theorem normalization_4620 (c2_depth c2_kind c2_sign r3_level : Int) : (¬ (formula_1255 c2_depth c2_kind c2_sign r3_level)) ↔ (¬ (shared_expr_Repair047_92 c2_depth c2_kind c2_sign r3_level)) := (not_congr (normalization_4619 c2_depth c2_kind c2_sign r3_level))

abbrev shared_expr_Repair047_93 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair047_92 c2_depth c2_kind c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
theorem normalization_4621 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : (formula_1256 c2_depth c2_kind c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_93 c2_depth c2_kind c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_4620 c2_depth c2_kind c2_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_1076 c2_kind)))

theorem normalization_4622 (c2_depth c2_kind c2_sign r3_group r3_level : Int) : (¬ (formula_1256 c2_depth c2_kind c2_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair047_93 c2_depth c2_kind c2_sign r3_group r3_level)) := (not_congr (normalization_4621 c2_depth c2_kind c2_sign r3_group r3_level))

theorem normalization_4623 (c2_depth c2_kind c2_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_1256 c2_depth c2_kind c2_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair047_93 c2_depth c2_kind c2_sign r3_group r3_level))) := (or_congr (normalization_4616 r3_mode) (or_congr (normalization_4618 r3_mode) (normalization_4622 c2_depth c2_kind c2_sign r3_group r3_level)))

theorem normalization_4624 (c2_depth c2_kind c2_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_1256 c2_depth c2_kind c2_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair047_93 c2_depth c2_kind c2_sign r3_group r3_level)))) := (not_congr (normalization_4623 c2_depth c2_kind c2_sign r3_group r3_level r3_mode))

theorem normalization_4625 (r3_mode : Int) : (r3_mode ≤ (2 : Int)) ↔ ((r3_mode) ≤ (2 : Int)) := by
  omega

theorem normalization_4626 (r3_mode : Int) : (¬ (r3_mode ≤ (2 : Int))) ↔ (¬ ((r3_mode) ≤ (2 : Int))) := (not_congr (normalization_4625 r3_mode))

theorem normalization_4627 (r3_mode : Int) : (r3_mode ≥ (2 : Int)) ↔ (¬ ((r3_mode) ≤ (1 : Int))) := by
  omega

theorem normalization_4628 (r3_mode : Int) : (¬ (r3_mode ≥ (2 : Int))) ↔ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) := (not_congr (normalization_4627 r3_mode))

theorem normalization_4629 (c2_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4630 (c2_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_4629 c2_depth r3_level))

theorem normalization_4631 (c2_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4632 (c2_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4631 c2_depth r3_level))

abbrev shared_expr_Repair047_94 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_4633 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : (formula_1257 c2_depth c2_kind c2_node c2_sign r3_level) ↔ (shared_expr_Repair047_94 c2_depth c2_kind c2_node c2_sign r3_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1068 c2_sign) (or_congr (normalization_1090 c2_node) (or_congr (normalization_4630 c2_depth r3_level) (normalization_4632 c2_depth r3_level))))))

theorem normalization_4634 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : (¬ (formula_1257 c2_depth c2_kind c2_node c2_sign r3_level)) ↔ (¬ (shared_expr_Repair047_94 c2_depth c2_kind c2_node c2_sign r3_level)) := (not_congr (normalization_4633 c2_depth c2_kind c2_node c2_sign r3_level))

abbrev shared_expr_Repair047_95 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair047_94 c2_depth c2_kind c2_node c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair047_90 c2_depth c2_kind c2_sign r3_level))))
theorem normalization_4635 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (formula_1258 c2_depth c2_kind c2_node c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_95 c2_depth c2_kind c2_node c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_4634 c2_depth c2_kind c2_node c2_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_4610 c2_depth c2_kind c2_sign r3_level)))

theorem normalization_4636 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (¬ (formula_1258 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair047_95 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) := (not_congr (normalization_4635 c2_depth c2_kind c2_node c2_sign r3_group r3_level))

theorem normalization_4637 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_1258 c2_depth c2_kind c2_node c2_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair047_95 c2_depth c2_kind c2_node c2_sign r3_group r3_level))) := (or_congr (normalization_4626 r3_mode) (or_congr (normalization_4628 r3_mode) (normalization_4636 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))

theorem normalization_4638 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_1258 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair047_95 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) := (not_congr (normalization_4637 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))

theorem normalization_4639 (r3_mode : Int) : (r3_mode ≤ (3 : Int)) ↔ ((r3_mode) ≤ (3 : Int)) := by
  omega

theorem normalization_4640 (r3_mode : Int) : (¬ (r3_mode ≤ (3 : Int))) ↔ (¬ ((r3_mode) ≤ (3 : Int))) := (not_congr (normalization_4639 r3_mode))

theorem normalization_4641 (r3_mode : Int) : (r3_mode ≥ (3 : Int)) ↔ (¬ ((r3_mode) ≤ (2 : Int))) := by
  omega

theorem normalization_4642 (r3_mode : Int) : (¬ (r3_mode ≥ (3 : Int))) ↔ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) := (not_congr (normalization_4641 r3_mode))

abbrev shared_expr_Repair047_96 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_4643 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : (formula_1259 c2_depth c2_kind c2_node c2_sign r3_level) ↔ (shared_expr_Repair047_96 c2_depth c2_kind c2_node c2_sign r3_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1068 c2_sign) (or_congr (normalization_1102 c2_node) (or_congr (normalization_4630 c2_depth r3_level) (normalization_4632 c2_depth r3_level))))))

theorem normalization_4644 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : (¬ (formula_1259 c2_depth c2_kind c2_node c2_sign r3_level)) ↔ (¬ (shared_expr_Repair047_96 c2_depth c2_kind c2_node c2_sign r3_level)) := (not_congr (normalization_4643 c2_depth c2_kind c2_node c2_sign r3_level))

abbrev shared_expr_Repair047_97 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair047_96 c2_depth c2_kind c2_node c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair047_90 c2_depth c2_kind c2_sign r3_level))))
theorem normalization_4645 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (formula_1260 c2_depth c2_kind c2_node c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_97 c2_depth c2_kind c2_node c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_4644 c2_depth c2_kind c2_node c2_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_4610 c2_depth c2_kind c2_sign r3_level)))

theorem normalization_4646 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (¬ (formula_1260 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair047_97 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) := (not_congr (normalization_4645 c2_depth c2_kind c2_node c2_sign r3_group r3_level))

theorem normalization_4647 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_1260 c2_depth c2_kind c2_node c2_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair047_97 c2_depth c2_kind c2_node c2_sign r3_group r3_level))) := (or_congr (normalization_4640 r3_mode) (or_congr (normalization_4642 r3_mode) (normalization_4646 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))

theorem normalization_4648 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_1260 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair047_97 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) := (not_congr (normalization_4647 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))

theorem normalization_4649 (r3_mode : Int) : (r3_mode ≤ (4 : Int)) ↔ ((r3_mode) ≤ (4 : Int)) := by
  omega

theorem normalization_4650 (r3_mode : Int) : (¬ (r3_mode ≤ (4 : Int))) ↔ (¬ ((r3_mode) ≤ (4 : Int))) := (not_congr (normalization_4649 r3_mode))

theorem normalization_4651 (r3_mode : Int) : (¬ (r3_mode ≥ (4 : Int))) ↔ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) := (not_congr (normalization_1242 r3_mode))

abbrev shared_expr_Repair047_98 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_4652 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : (formula_1261 c2_depth c2_kind c2_node c2_sign r3_level) ↔ (shared_expr_Repair047_98 c2_depth c2_kind c2_node c2_sign r3_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1082 c2_sign) (or_congr (normalization_1090 c2_node) (or_congr (normalization_4630 c2_depth r3_level) (normalization_4632 c2_depth r3_level))))))

theorem normalization_4653 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : (¬ (formula_1261 c2_depth c2_kind c2_node c2_sign r3_level)) ↔ (¬ (shared_expr_Repair047_98 c2_depth c2_kind c2_node c2_sign r3_level)) := (not_congr (normalization_4652 c2_depth c2_kind c2_node c2_sign r3_level))

abbrev shared_expr_Repair047_99 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair047_92 c2_depth c2_kind c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair047_98 c2_depth c2_kind c2_node c2_sign r3_level))))
theorem normalization_4654 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (formula_1262 c2_depth c2_kind c2_node c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_99 c2_depth c2_kind c2_node c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_4620 c2_depth c2_kind c2_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_4653 c2_depth c2_kind c2_node c2_sign r3_level)))

theorem normalization_4655 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (¬ (formula_1262 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair047_99 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) := (not_congr (normalization_4654 c2_depth c2_kind c2_node c2_sign r3_group r3_level))

theorem normalization_4656 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_1262 c2_depth c2_kind c2_node c2_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair047_99 c2_depth c2_kind c2_node c2_sign r3_group r3_level))) := (or_congr (normalization_4650 r3_mode) (or_congr (normalization_4651 r3_mode) (normalization_4655 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))

theorem normalization_4657 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_1262 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair047_99 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) := (not_congr (normalization_4656 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))

theorem normalization_4658 (r3_mode : Int) : (r3_mode ≤ (5 : Int)) ↔ ((r3_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_4659 (r3_mode : Int) : (¬ (r3_mode ≤ (5 : Int))) ↔ (¬ ((r3_mode) ≤ (5 : Int))) := (not_congr (normalization_4658 r3_mode))

theorem normalization_4660 (r3_mode : Int) : (r3_mode ≥ (5 : Int)) ↔ (¬ ((r3_mode) ≤ (4 : Int))) := by
  omega

theorem normalization_4661 (r3_mode : Int) : (¬ (r3_mode ≥ (5 : Int))) ↔ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) := (not_congr (normalization_4660 r3_mode))

abbrev shared_expr_Repair047_100 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : Prop := ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c2_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c2_node / (2 : Int))) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_4662 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : (formula_1263 c2_depth c2_kind c2_node c2_sign r3_level) ↔ (shared_expr_Repair047_100 c2_depth c2_kind c2_node c2_sign r3_level) := (or_congr (normalization_101 c2_kind) (or_congr (normalization_103 c2_kind) (or_congr (normalization_1082 c2_sign) (or_congr (normalization_1102 c2_node) (or_congr (normalization_4630 c2_depth r3_level) (normalization_4632 c2_depth r3_level))))))

theorem normalization_4663 (c2_depth c2_kind c2_node c2_sign r3_level : Int) : (¬ (formula_1263 c2_depth c2_kind c2_node c2_sign r3_level)) ↔ (¬ (shared_expr_Repair047_100 c2_depth c2_kind c2_node c2_sign r3_level)) := (not_congr (normalization_4662 c2_depth c2_kind c2_node c2_sign r3_level))

abbrev shared_expr_Repair047_101 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair047_92 c2_depth c2_kind c2_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair047_100 c2_depth c2_kind c2_node c2_sign r3_level))))
theorem normalization_4664 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (formula_1264 c2_depth c2_kind c2_node c2_sign r3_group r3_level) ↔ (shared_expr_Repair047_101 c2_depth c2_kind c2_node c2_sign r3_group r3_level) := (or_congr (and_congr (normalization_2714 r3_group) (normalization_4620 c2_depth c2_kind c2_sign r3_level)) (and_congr (not_congr (normalization_2714 r3_group)) (normalization_4663 c2_depth c2_kind c2_node c2_sign r3_level)))

theorem normalization_4665 (c2_depth c2_kind c2_node c2_sign r3_group r3_level : Int) : (¬ (formula_1264 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) ↔ (¬ (shared_expr_Repair047_101 c2_depth c2_kind c2_node c2_sign r3_group r3_level)) := (not_congr (normalization_4664 c2_depth c2_kind c2_node c2_sign r3_group r3_level))

theorem normalization_4666 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_1264 c2_depth c2_kind c2_node c2_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair047_101 c2_depth c2_kind c2_node c2_sign r3_group r3_level))) := (or_congr (normalization_4659 r3_mode) (or_congr (normalization_4661 r3_mode) (normalization_4665 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))

theorem normalization_4667 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_1264 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair047_101 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) := (not_congr (normalization_4666 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair047_102 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair047_91 c2_depth c2_kind c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair047_93 c2_depth c2_kind c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair047_95 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair047_97 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair047_99 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair047_101 c2_depth c2_kind c2_node c2_sign r3_group r3_level)))))
theorem normalization_4668 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_1265 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_102 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) := (or_congr (normalization_4614 c2_depth c2_kind c2_sign r3_group r3_level r3_mode) (or_congr (normalization_4624 c2_depth c2_kind c2_sign r3_group r3_level r3_mode) (or_congr (normalization_4638 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (or_congr (normalization_4648 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (or_congr (normalization_4657 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (normalization_4667 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))))))

theorem normalization_4669 (c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode : Int) : ((formula_1322 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) ↔ (formula_1265 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)) ↔ ((shared_expr_Repair047_68 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_102 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)) := (iff_congr (normalization_4513 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (normalization_4668 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))

abbrev shared_expr_Repair047_103 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair047_102 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))
theorem normalization_4670 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_1338 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_103 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_1003 c2_kind) (normalization_4602 c2_group c2_level c2_mode r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_1003 c2_kind)) (normalization_4668 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)))

abbrev shared_expr_Repair047_104 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Repair047_69 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_103 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))
theorem normalization_4671 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_1339 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_104 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := (iff_congr (normalization_4514 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) (normalization_4670 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_2723 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode : Int) : (formula_1339 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_1104 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Repair047_0 c2_group c2_level c2_mode r3_group r3_level r3_mode) (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode) (shared_expr_Repair047_68 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (shared_expr_Repair047_102 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode))
  have n0 : ((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1005 c2_kind) (replay_172 c2_kind)
  have n1 : ((shared_expr_Repair047_0 c2_group c2_level c2_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Repair047_87 c2_group c2_level c2_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_4604 c2_group c2_level c2_mode r3_group r3_level r3_mode) (replay_2721 c2_group c2_level c2_mode r3_group r3_level r3_mode)
  have n2 : ((shared_expr_Repair047_68 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) ↔ (shared_expr_Repair047_102 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_4669 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode) (replay_2722 c2_depth c2_kind c2_node c2_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_4671 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r3_group r3_level r3_mode) hn

end H4Formal.Generated.Repair
