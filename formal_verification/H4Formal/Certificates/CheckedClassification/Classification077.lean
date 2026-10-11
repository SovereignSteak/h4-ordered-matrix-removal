import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification076

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Classification077_0 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ ((formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True))
abbrev formula_2102 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_0 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_1747 (p0 p1 : Prop) : (((p0 ↔ p1)) → ((p0 ↔ True) ↔ (p1 ↔ True))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_1 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
abbrev shared_expr_Classification077_2 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_3 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_2 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification077_4 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_5 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_4 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification077_6 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_7 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((shared_expr_Classification077_6 c3_depth c3_kind c3_sign r1_level) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_8 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_2 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_7 c3_depth c3_kind c3_node c3_sign r1_level)))
abbrev shared_expr_Classification077_9 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((shared_expr_Classification077_6 c3_depth c3_kind c3_sign r1_level) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_10 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_2 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_9 c3_depth c3_kind c3_node c3_sign r1_level)))
abbrev shared_expr_Classification077_11 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_12 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((shared_expr_Classification077_11 c3_depth c3_kind c3_sign r1_level) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_13 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_12 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_4 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification077_14 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((shared_expr_Classification077_11 c3_depth c3_kind c3_sign r1_level) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_15 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_14 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_4 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification077_16 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_3 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_5 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification077_8 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification077_10 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification077_13 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification077_15 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
abbrev shared_expr_Classification077_17 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_1 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_16 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
abbrev shared_expr_Classification077_18 (c3_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_19 (c3_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_20 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_18 c3_level r1_depth r1_kind r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_19 c3_level r1_depth r1_kind r1_sign)))
abbrev shared_expr_Classification077_21 (c3_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_22 (c3_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_23 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_21 c3_level r1_depth r1_kind r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_22 c3_level r1_depth r1_kind r1_sign)))
abbrev shared_expr_Classification077_24 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_18 c3_level r1_depth r1_kind r1_sign) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_25 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_24 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_26 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_18 c3_level r1_depth r1_kind r1_sign) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_27 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_26 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_28 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_22 c3_level r1_depth r1_kind r1_sign) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_29 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_28 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_30 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_22 c3_level r1_depth r1_kind r1_sign) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_31 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_30 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_32 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_20 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((((c3_mode) ≤ (1 : Int)) ∧ (¬ ((c3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_23 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((((c3_mode) ≤ (2 : Int)) ∧ (¬ ((c3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification077_25 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (3 : Int)) ∧ (¬ ((c3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification077_27 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (4 : Int)) ∧ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification077_29 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (5 : Int)) ∧ (¬ ((c3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification077_31 c3_group c3_level r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Classification077_33 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_34 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ∧ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_35 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification077_33 c3_node c3_sign h r1_depth r1_node r1_sign) ∨ (shared_expr_Classification077_34 c3_node c3_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Classification077_36 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
abbrev shared_expr_Classification077_37 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
abbrev shared_expr_Classification077_38 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification077_36 c3_node c3_sign r1_node r1_sign) ∨ (shared_expr_Classification077_37 c3_node c3_sign r1_node r1_sign)))
abbrev shared_expr_Classification077_39 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification077_35 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (shared_expr_Classification077_38 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))
abbrev shared_expr_Classification077_40 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Classification077_39 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Classification077_41 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ True) ∨ (shared_expr_Classification077_40 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign))
abbrev shared_expr_Classification077_42 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_32 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_41 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Classification077_43 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_17 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_42 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_6687 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ ((shared_expr_Classification077_43 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) := (iff_congr (normalization_6627 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_145))

abbrev shared_expr_Classification077_44 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_45 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_2 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_44 c3_depth c3_kind c3_node c3_sign r1_level)))
abbrev shared_expr_Classification077_46 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_47 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_2 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_46 c3_depth c3_kind c3_node c3_sign r1_level)))
abbrev shared_expr_Classification077_48 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_49 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_48 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_4 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification077_50 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_51 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_50 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_4 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification077_52 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_3 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_5 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification077_45 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification077_47 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification077_49 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification077_51 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
abbrev shared_expr_Classification077_53 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_1 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_52 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
abbrev shared_expr_Classification077_54 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_55 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_54 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_56 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_57 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_56 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_58 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification077_59 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_58 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_60 (c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification077_61 (c3_group c3_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_60 c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification077_62 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_20 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((((c3_mode) ≤ (1 : Int)) ∧ (¬ ((c3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_23 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((((c3_mode) ≤ (2 : Int)) ∧ (¬ ((c3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification077_55 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (3 : Int)) ∧ (¬ ((c3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification077_57 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (4 : Int)) ∧ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification077_59 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c3_mode) ≤ (5 : Int)) ∧ (¬ ((c3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification077_61 c3_group c3_level r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Classification077_63 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification077_64 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification077_36 c3_node c3_sign r1_node r1_sign) ∨ (shared_expr_Classification077_63 c3_node c3_sign r1_node r1_sign)))
abbrev shared_expr_Classification077_65 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_34 c3_node c3_sign h r1_depth r1_node r1_sign) ∨ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification077_33 c3_node c3_sign h r1_depth r1_node r1_sign))
abbrev shared_expr_Classification077_66 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ∨ (shared_expr_Classification077_64 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) ∨ (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification077_65 c3_node c3_sign h r1_depth r1_node r1_sign)))
abbrev shared_expr_Classification077_67 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_62 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_66 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Classification077_68 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_53 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_67 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_6688 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ ((shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) := (iff_congr (normalization_6685 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_145))

abbrev shared_expr_Classification077_69 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((shared_expr_Classification077_43 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ ((shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True))
theorem normalization_6689 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2102 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_69 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_6687 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_6688 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification077_70 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_43 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem replay_4908 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2102 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_1747 (shared_expr_Classification077_43 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : (shared_expr_Classification077_70 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
    exact Iff.mp (normalization_6686 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_4907 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_6689 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Classification077_71 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ (formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_2103 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_71 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_1748 (p0 : Prop) : ((p0 ↔ True) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_72 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_6690 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2103 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_72 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_6688 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_6685 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_4909 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2103 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_1748 (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_6690 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Classification077_73 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ (formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_2104 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_73 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_1749 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_74 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((shared_expr_Classification077_43 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ↔ (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_6691 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2104 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_74 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_6687 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_6685 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of trans.
theorem replay_4910 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2104 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_1749 ((shared_expr_Classification077_43 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) ((shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True) (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : (shared_expr_Classification077_69 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
    exact Iff.mp (normalization_6689 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_4908 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have n1 : (shared_expr_Classification077_72 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
    exact Iff.mp (normalization_6690 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_4909 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6691 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_4911 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i277 : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_4910 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) i277

abbrev shared_expr_Classification077_75 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((formula_2099 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_2099 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign))
abbrev formula_2105 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_75 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)

theorem normalized_1750 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_76 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_67 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification077_67 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign))
theorem normalization_6692 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2105 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification077_76 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := (iff_congr (normalization_6684 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) (normalization_6684 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_4912 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2105 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := by
  classical
  have ht := (normalized_1750 (shared_expr_Classification077_67 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_6692 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) hn

abbrev shared_expr_Classification077_77 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_2106 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_77 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_1751 (p0 p1 : Prop) : (((p0 ↔ p0)) → (p1 ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_78 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_6693 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2106 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_78 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_6685 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_6685 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_4913 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2106 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_1751 (shared_expr_Classification077_67 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : (shared_expr_Classification077_76 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := by
    exact Iff.mp (normalization_6692 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) (replay_4912 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)
  have hn := ht n0
  exact Iff.mpr (normalization_6693 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_4914 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i277 : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_4913 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_4911 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i277)

theorem normalized_1752 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of rewrite.
theorem replay_4915 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2106 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_1752 (shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_6693 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_4916 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i277 : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_4915 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_4914 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i277)

-- Checked replay of mp.
theorem replay_4917 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i277 : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_4913 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_4916 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i277)

-- Checked replay of mp.
theorem replay_4918 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i277 : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_4913 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_4917 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i277)

abbrev shared_expr_Classification077_79 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ (c3_kind = (2 : Int))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2107 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Classification077_79 c3_depth c3_kind c3_sign r1_group r1_level)

abbrev shared_expr_Classification077_80 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ (c3_kind = (2 : Int))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2108 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Classification077_80 c3_depth c3_kind c3_sign r1_group r1_level)

abbrev shared_expr_Classification077_81 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int)))))
abbrev formula_2109 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Classification077_81 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Classification077_82 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int)))))
abbrev formula_2110 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Classification077_82 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Classification077_83 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int)))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2111 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Classification077_83 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Classification077_84 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((r1_group = (1 : Int)) ∧ ((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int)))) ∨ ((¬ (r1_group = (1 : Int))) ∧ ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))))))
abbrev formula_2112 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Classification077_84 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Classification077_85 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (0 : Int)) ∧ (formula_2107 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((r1_mode = (1 : Int)) ∧ (formula_2108 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((r1_mode = (2 : Int)) ∧ (formula_2109 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((r1_mode = (3 : Int)) ∧ (formula_2110 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((r1_mode = (4 : Int)) ∧ (formula_2111 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((r1_mode = (5 : Int)) ∧ (formula_2112 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
abbrev formula_2113 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification077_85 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

abbrev shared_expr_Classification077_86 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((c3_kind = (0 : Int)) ∧ ((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group)))) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2113 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
abbrev formula_2114 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification077_86 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)

abbrev shared_expr_Classification077_87 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (((c3_group = (1 : Int)) ∧ ((r1_kind = (1 : Int)) ∧ (r1_depth = c3_level) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))))) ∨ ((¬ (c3_group = (1 : Int))) ∧ ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))))))
abbrev formula_2115 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Classification077_87 c3_group c3_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Classification077_88 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (((c3_group = (1 : Int)) ∧ ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))))) ∨ ((¬ (c3_group = (1 : Int))) ∧ ((r1_kind = (1 : Int)) ∧ (r1_depth = c3_level) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))))))
abbrev formula_2116 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Classification077_88 c3_group c3_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Classification077_89 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((c3_mode = (0 : Int)) ∧ (formula_2115 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((c3_mode = (1 : Int)) ∧ (formula_2116 c3_group c3_level r1_depth r1_kind r1_sign)) ∨ ((c3_mode = (2 : Int)) ∧ (formula_2091 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c3_mode = (3 : Int)) ∧ (formula_2092 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c3_mode = (4 : Int)) ∧ (formula_2093 c3_group c3_level r1_depth r1_kind r1_node r1_sign)) ∨ ((c3_mode = (5 : Int)) ∧ (formula_2094 c3_group c3_level r1_depth r1_kind r1_node r1_sign)))
abbrev formula_2117 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_89 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Classification077_90 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ ((r1_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ ((r1_sign = (1 : Int)) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))
abbrev formula_2118 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_90 c3_node c3_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Classification077_91 (c3_node c3_sign r1_node r1_sign : Int) : Prop := ((((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c3_sign = (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ∨ (((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_2119 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_91 c3_node c3_sign r1_node r1_sign)

abbrev shared_expr_Classification077_92 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((r1_kind = (2 : Int)) ∨ (c3_kind = (2 : Int)) ∨ ((r1_depth = c3_depth) ∧ (formula_2118 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (((r1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ (formula_2119 c3_node c3_sign r1_node r1_sign)))
abbrev formula_2120 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_92 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Classification077_93 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((c3_kind = (0 : Int)) ∧ (formula_2117 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2120 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev formula_2121 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_93 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Classification077_94 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((r1_kind = (0 : Int)) ∧ (formula_2114 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) ∨ ((¬ (r1_kind = (0 : Int))) ∧ (formula_2121 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev formula_2122 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_94 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Classification077_95 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_2100 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_2122 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_2123 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Classification077_95 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

set_option maxHeartbeats 2000000 in
theorem normalized_1753 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p16 ∧ (¬ p17)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)) ∨ (((¬ p52) ∧ p53) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p54) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p55))))) ∨ (((¬ p53) ∧ p56) ∧ (((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p59)) ∨ ((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p59)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p60))))))))) ↔ (((p0 ∧ (¬ p1)) ∧ (((p2 ∧ (¬ p3)) ∧ (((¬ p4) ∧ p5) ∧ ((¬ p6) ∧ p7) ∧ (¬ ((¬ p8) ∧ p9)))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p10 ∧ (¬ p11)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p22 ∧ (¬ p10)) ∧ (((p12 ∧ (¬ p13)) ∧ (p14 ∧ (¬ p15))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p23 ∧ (¬ p22)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))))) ∨ ((p27 ∧ (¬ p23)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p18 ∧ (¬ p19)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))))) ∨ ((p29 ∧ (¬ p27)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p25) ∧ p26))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))) ∨ ((p30 ∧ (¬ p29)) ∧ (((p12 ∧ (¬ p13)) ∧ ((p15 ∧ (¬ p2)) ∧ (p24 ∧ (¬ p16)) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))) ∧ ((¬ p28) ∧ p25))) ∨ ((¬ (p12 ∧ (¬ p13))) ∧ ((p15 ∧ (¬ p2)) ∧ ((¬ p17) ∧ p16) ∧ ((p21 ∧ (¬ p18)) ∨ (p20 ∧ (¬ p21))))))))))) ∨ ((¬ (p0 ∧ (¬ p1))) ∧ (((p2 ∧ (¬ p3)) ∧ (((p31 ∧ (¬ p32)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p43 ∧ (¬ p31)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p37) ∧ p42) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))))))) ∨ ((p44 ∧ (¬ p43)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p48 ∧ (¬ p44)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p50 ∧ (¬ p48)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p45) ∧ p46))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))) ∨ ((p51 ∧ (¬ p50)) ∧ (((p33 ∧ (¬ p34)) ∧ ((p35 ∧ (¬ p0)) ∧ ((¬ p36) ∧ p37) ∧ ((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ ((¬ p49) ∧ p45))) ∨ ((¬ (p33 ∧ (¬ p34))) ∧ (p47 ∧ (¬ p35))))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ ((p47 ∧ (¬ p35)) ∨ (p14 ∧ (¬ p15)) ∨ (((¬ p53) ∧ p56) ∧ (((p38 ∧ (¬ p39)) ∧ (p18 ∧ (¬ p19)) ∧ (¬ p59)) ∨ ((p40 ∧ (¬ p41)) ∧ (p20 ∧ (¬ p21)) ∧ ((¬ p57) ∧ p58) ∧ (¬ p59)) ∨ ((p41 ∧ (¬ p38)) ∧ (p21 ∧ (¬ p18)) ∧ (¬ p58) ∧ (¬ p60)))) ∨ (((¬ p52) ∧ p53) ∧ ((((p38 ∧ (¬ p39)) ∨ (p40 ∧ (¬ p41))) ∧ (p18 ∧ (¬ p19)) ∧ p54) ∨ (((p41 ∧ (¬ p38)) ∨ (p40 ∧ (¬ p41))) ∧ (p21 ∧ (¬ p18)) ∧ (¬ (¬ p55))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6694 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

abbrev shared_expr_Classification077_96 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
theorem normalization_6695 (c3_depth c3_kind c3_sign r1_level : Int) : ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (shared_expr_Classification077_96 c3_depth c3_kind c3_sign r1_level) := (and_congr (normalization_6546 c3_kind) (and_congr (normalization_6694 c3_depth r1_level) (normalization_6550 c3_sign)))

abbrev shared_expr_Classification077_97 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_96 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_6696 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2107 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Classification077_97 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_5 r1_group) (normalization_6545 c3_kind)) (and_congr (not_congr (normalization_5 r1_group)) (normalization_6695 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_6697 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (0 : Int)) ∧ (formula_2107 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_97 c3_depth c3_kind c3_sign r1_group r1_level)) := (and_congr (normalization_17 r1_mode) (normalization_6696 c3_depth c3_kind c3_sign r1_group r1_level))

abbrev shared_expr_Classification077_98 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
theorem normalization_6698 (c3_depth c3_kind c3_sign r1_level : Int) : ((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (shared_expr_Classification077_98 c3_depth c3_kind c3_sign r1_level) := (and_congr (normalization_6546 c3_kind) (and_congr (normalization_6694 c3_depth r1_level) (normalization_6555 c3_sign)))

abbrev shared_expr_Classification077_99 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_98 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_6699 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2108 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Classification077_99 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_5 r1_group) (normalization_6545 c3_kind)) (and_congr (not_congr (normalization_5 r1_group)) (normalization_6698 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_6700 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (1 : Int)) ∧ (formula_2108 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_99 c3_depth c3_kind c3_sign r1_group r1_level)) := (and_congr (normalization_5712 r1_mode) (normalization_6699 c3_depth c3_kind c3_sign r1_group r1_level))

abbrev shared_expr_Classification077_100 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_96 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_44 c3_depth c3_kind c3_node c3_sign r1_level)))
theorem normalization_6701 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2109 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Classification077_100 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_5 r1_group) (normalization_6695 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_5 r1_group)) (normalization_6638 c3_depth c3_kind c3_node c3_sign r1_level)))

theorem normalization_6702 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (2 : Int)) ∧ (formula_2109 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification077_100 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_5716 r1_mode) (normalization_6701 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Classification077_101 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_96 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_46 c3_depth c3_kind c3_node c3_sign r1_level)))
theorem normalization_6703 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2110 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Classification077_101 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_5 r1_group) (normalization_6695 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_5 r1_group)) (normalization_6641 c3_depth c3_kind c3_node c3_sign r1_level)))

theorem normalization_6704 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (3 : Int)) ∧ (formula_2110 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification077_101 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_5722 r1_mode) (normalization_6703 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Classification077_102 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_48 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_98 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_6705 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2111 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Classification077_102 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_5 r1_group) (normalization_6644 c3_depth c3_kind c3_node c3_sign r1_level)) (and_congr (not_congr (normalization_5 r1_group)) (normalization_6698 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_6706 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (4 : Int)) ∧ (formula_2111 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification077_102 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_5726 r1_mode) (normalization_6705 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Classification077_103 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_50 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification077_98 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_6707 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2112 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Classification077_103 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_5 r1_group) (normalization_6647 c3_depth c3_kind c3_node c3_sign r1_level)) (and_congr (not_congr (normalization_5 r1_group)) (normalization_6698 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_6708 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((r1_mode = (5 : Int)) ∧ (formula_2112 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification077_103 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_5731 r1_mode) (normalization_6707 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Classification077_104 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_97 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_99 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification077_100 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification077_101 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification077_102 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification077_103 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
theorem normalization_6709 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2113 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification077_104 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := (or_congr (normalization_6697 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (or_congr (normalization_6700 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (or_congr (normalization_6702 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (or_congr (normalization_6704 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (or_congr (normalization_6706 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (normalization_6708 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))))))

abbrev shared_expr_Classification077_105 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_1 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_104 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
theorem normalization_6710 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2114 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification077_105 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_6540 c3_kind) (normalization_6630 c3_group c3_level c3_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_6540 c3_kind)) (normalization_6709 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))

theorem normalization_6711 (c3_level r1_depth : Int) : ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_6712 (c3_level r1_depth r1_kind r1_sign : Int) : ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int)))) ↔ (shared_expr_Classification077_19 c3_level r1_depth r1_kind r1_sign) := (and_congr (normalization_16 r1_kind) (and_congr (normalization_6711 c3_level r1_depth) (normalization_5738 r1_sign)))

theorem normalization_6713 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : (formula_2115 c3_group c3_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Classification077_20 c3_group c3_level r1_depth r1_kind r1_sign) := (or_congr (and_congr (normalization_6579 c3_group) (normalization_6581 c3_level r1_depth r1_kind r1_sign)) (and_congr (not_congr (normalization_6579 c3_group)) (normalization_6712 c3_level r1_depth r1_kind r1_sign)))

theorem normalization_6714 (c3_group c3_level c3_mode r1_depth r1_kind r1_sign : Int) : ((c3_mode = (0 : Int)) ∧ (formula_2115 c3_group c3_level r1_depth r1_kind r1_sign)) ↔ ((((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_20 c3_group c3_level r1_depth r1_kind r1_sign)) := (and_congr (normalization_6578 c3_mode) (normalization_6713 c3_group c3_level r1_depth r1_kind r1_sign))

theorem normalization_6715 (c3_level r1_depth r1_kind r1_sign : Int) : ((r1_kind = (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_level)) = (-1 : Int)) ∧ ((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int)))) ↔ (shared_expr_Classification077_21 c3_level r1_depth r1_kind r1_sign) := (and_congr (normalization_16 r1_kind) (and_congr (normalization_6711 c3_level r1_depth) (normalization_5744 r1_sign)))

theorem normalization_6716 (c3_group c3_level r1_depth r1_kind r1_sign : Int) : (formula_2116 c3_group c3_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Classification077_23 c3_group c3_level r1_depth r1_kind r1_sign) := (or_congr (and_congr (normalization_6579 c3_group) (normalization_6715 c3_level r1_depth r1_kind r1_sign)) (and_congr (not_congr (normalization_6579 c3_group)) (normalization_6588 c3_level r1_depth r1_kind r1_sign)))

theorem normalization_6717 (c3_group c3_level c3_mode r1_depth r1_kind r1_sign : Int) : ((c3_mode = (1 : Int)) ∧ (formula_2116 c3_group c3_level r1_depth r1_kind r1_sign)) ↔ ((((c3_mode) ≤ (1 : Int)) ∧ (¬ ((c3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification077_23 c3_group c3_level r1_depth r1_kind r1_sign)) := (and_congr (normalization_6586 c3_mode) (normalization_6716 c3_group c3_level r1_depth r1_kind r1_sign))

theorem normalization_6718 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : (formula_2117 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification077_62 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_6714 c3_group c3_level c3_mode r1_depth r1_kind r1_sign) (or_congr (normalization_6717 c3_group c3_level c3_mode r1_depth r1_kind r1_sign) (or_congr (normalization_6661 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) (or_congr (normalization_6664 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) (or_congr (normalization_6667 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) (normalization_6670 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign))))))

theorem normalization_6719 (c3_node r1_node : Int) : ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6720 (c3_node c3_sign r1_node r1_sign : Int) : ((r1_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_10 r1_sign) (and_congr (normalization_6548 c3_sign) (normalization_6719 c3_node r1_node)))

theorem normalization_6721 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((r1_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (shared_expr_Classification077_34 c3_node c3_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_25 r1_sign) (and_congr (normalization_6549 c3_sign) (and_congr (normalization_24 h r1_depth) (normalization_6719 c3_node r1_node))))

theorem normalization_6722 (c3_node r1_node : Int) : ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) ↔ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_6723 (c3_node r1_node : Int) : (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := (not_congr (normalization_6722 c3_node r1_node))

theorem normalization_6724 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((r1_sign = (1 : Int)) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification077_33 c3_node c3_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_26 r1_sign) (and_congr (normalization_6554 c3_sign) (and_congr (normalization_110 h r1_depth) (normalization_6723 c3_node r1_node))))

abbrev shared_expr_Classification077_106 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification077_34 c3_node c3_sign h r1_depth r1_node r1_sign) ∨ (shared_expr_Classification077_33 c3_node c3_sign h r1_depth r1_node r1_sign))
theorem normalization_6725 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2118 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification077_106 c3_node c3_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_6720 c3_node c3_sign r1_node r1_sign) (or_congr (normalization_6721 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6724 c3_node c3_sign h r1_depth r1_node r1_sign)))

theorem normalization_6726 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((r1_depth = c3_depth) ∧ (formula_2118 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification077_106 c3_node c3_sign h r1_depth r1_node r1_sign)) := (and_congr (normalization_6609 c3_depth r1_depth) (normalization_6725 c3_node c3_sign h r1_depth r1_node r1_sign))

theorem normalization_6727 (c3_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6728 (c3_node r1_node : Int) : ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_6729 (c3_node c3_sign r1_node r1_sign : Int) : (((r1_sign = (0 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c3_sign = (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (shared_expr_Classification077_36 c3_node c3_sign r1_node r1_sign) := (and_congr (normalization_5738 r1_sign) (and_congr (normalization_6548 c3_sign) (normalization_6728 c3_node r1_node)))

theorem normalization_6730 (c3_node r1_node : Int) : ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6731 (c3_node r1_node : Int) : (¬ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6730 c3_node r1_node))

theorem normalization_6732 (c3_node c3_sign r1_node r1_sign : Int) : (((r1_sign = (1 : Int)) ∨ (r1_sign = (2 : Int))) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))) ↔ (shared_expr_Classification077_63 c3_node c3_sign r1_node r1_sign) := (and_congr (normalization_5744 r1_sign) (and_congr (normalization_6554 c3_sign) (normalization_6731 c3_node r1_node)))

theorem normalization_6733 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2119 c3_node c3_sign r1_node r1_sign) ↔ ((shared_expr_Classification077_36 c3_node c3_sign r1_node r1_sign) ∨ (shared_expr_Classification077_63 c3_node c3_sign r1_node r1_sign)) := (or_congr (normalization_6729 c3_node c3_sign r1_node r1_sign) (normalization_6732 c3_node c3_sign r1_node r1_sign))

theorem normalization_6734 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : (((r1_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ (formula_2119 c3_node c3_sign r1_node r1_sign)) ↔ (shared_expr_Classification077_64 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) := (and_congr (normalization_6727 c3_depth r1_depth) (normalization_6733 c3_node c3_sign r1_node r1_sign))

abbrev shared_expr_Classification077_107 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ∨ (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification077_106 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (shared_expr_Classification077_64 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))
theorem normalization_6735 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2120 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification077_107 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_34 r1_kind) (or_congr (normalization_6545 c3_kind) (or_congr (normalization_6726 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6734 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))))

abbrev shared_expr_Classification077_108 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_62 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_107 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_6736 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2121 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification077_108 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_6540 c3_kind) (normalization_6718 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) (and_congr (not_congr (normalization_6540 c3_kind)) (normalization_6735 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Classification077_109 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification077_105 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification077_108 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_6737 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2122 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_109 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (and_congr (normalization_0 r1_kind) (normalization_6710 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_0 r1_kind)) (normalization_6736 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Classification077_110 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Classification077_68 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_109 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_6738 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2123 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Classification077_110 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_6685 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_6737 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_4919 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_2123 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_1753 ((r1_kind) ≤ (0 : Int)) ((r1_kind) ≤ (-1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ((r1_mode) ≤ (0 : Int)) ((r1_mode) ≤ (-1 : Int)) ((r1_group) ≤ (1 : Int)) ((r1_group) ≤ (0 : Int)) ((c3_kind) ≤ (2 : Int)) ((c3_kind) ≤ (1 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (2 : Int)) ((c3_sign) ≤ (1 : Int)) ((r1_mode) ≤ (1 : Int)) ((r1_mode) ≤ (2 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((r1_mode) ≤ (3 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int)) ((r1_mode) ≤ (4 : Int)) ((r1_mode) ≤ (5 : Int)) ((c3_mode) ≤ (0 : Int)) ((c3_mode) ≤ (-1 : Int)) ((c3_group) ≤ (1 : Int)) ((c3_group) ≤ (0 : Int)) ((r1_kind) ≤ (1 : Int)) ((c3_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)) ((r1_sign) ≤ (2 : Int)) ((r1_sign) ≤ (1 : Int)) ((c3_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ((c3_mode) ≤ (1 : Int)) ((c3_mode) ≤ (2 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((r1_kind) ≤ (2 : Int)) ((c3_mode) ≤ (3 : Int)) ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int)) ((c3_mode) ≤ (4 : Int)) ((c3_mode) ≤ (5 : Int)) ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)) ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6738 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_4920 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i277 : ((formula_2080 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_2122 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_4919 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_4918 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i277)

theorem normalized_1754 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6739 (c3_kind : Int) : (c3_kind ≤ (0 : Int)) ↔ ((c3_kind) ≤ (0 : Int)) := by
  omega

theorem normalization_6740 (c3_kind : Int) : (c3_kind ≥ (0 : Int)) ↔ (¬ ((c3_kind) ≤ (-1 : Int))) := by
  omega

theorem normalization_6741 (c3_kind : Int) : ((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int))) ↔ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) := (and_congr (normalization_6739 c3_kind) (normalization_6740 c3_kind))

theorem normalization_6742 (c3_kind : Int) : ((c3_kind = (0 : Int)) ↔ ((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int)))) ↔ ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) := (iff_congr (normalization_6540 c3_kind) (normalization_6741 c3_kind))

-- Checked replay of rewrite.
theorem replay_4921 (c3_kind : Int) : ((c3_kind = (0 : Int)) ↔ ((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1754 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6742 c3_kind) hn

theorem normalized_1755 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6743 (c3_kind : Int) : (¬ (c3_kind ≤ (0 : Int))) ↔ (¬ ((c3_kind) ≤ (0 : Int))) := (not_congr (normalization_6739 c3_kind))

theorem normalization_6744 (c3_kind : Int) : (¬ (c3_kind ≥ (0 : Int))) ↔ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) := (not_congr (normalization_6740 c3_kind))

theorem normalization_6745 (c3_kind : Int) : ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) := (or_congr (normalization_6743 c3_kind) (normalization_6744 c3_kind))

theorem normalization_6746 (c3_kind : Int) : (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := (not_congr (normalization_6745 c3_kind))

theorem normalization_6747 (c3_kind : Int) : (((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := (iff_congr (normalization_6741 c3_kind) (normalization_6746 c3_kind))

-- Checked replay of rewrite.
theorem replay_4922 (c3_kind : Int) : (((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1755 ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6747 c3_kind) hn

theorem normalized_1756 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6748 (c3_kind : Int) : ((c3_kind = (0 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := (iff_congr (normalization_6540 c3_kind) (normalization_6746 c3_kind))

-- Checked replay of trans.
theorem replay_4923 (c3_kind : Int) : ((c3_kind = (0 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1756 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))))
  have n0 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_6742 c3_kind) (replay_4921 c3_kind)
  have n1 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6747 c3_kind) (replay_4922 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6748 c3_kind) hn

theorem normalized_1757 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6749 (c3_mode r1_mode : Int) : (r1_mode ≤ c3_mode) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6750 (c3_mode r1_mode : Int) : (r1_mode ≥ c3_mode) ↔ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_6751 (c3_mode r1_mode : Int) : ((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (and_congr (normalization_6749 c3_mode r1_mode) (normalization_6750 c3_mode r1_mode))

abbrev shared_expr_Classification077_111 (c3_mode r1_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
theorem normalization_6752 (c3_mode r1_mode : Int) : ((r1_mode = c3_mode) ↔ ((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode))) ↔ (shared_expr_Classification077_111 c3_mode r1_mode) := (iff_congr (normalization_6541 c3_mode r1_mode) (normalization_6751 c3_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_4924 (c3_mode r1_mode : Int) : ((r1_mode = c3_mode) ↔ ((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode))) := by
  classical
  have ht := (normalized_1757 ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6752 c3_mode r1_mode) hn

theorem normalized_1758 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6753 (c3_mode r1_mode : Int) : ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6754 (c3_mode r1_mode : Int) : ((r1_mode ≤ c3_mode) ↔ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_6749 c3_mode r1_mode) (normalization_6753 c3_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_4925 (c3_mode r1_mode : Int) : ((r1_mode ≤ c3_mode) ↔ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1758 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6754 c3_mode r1_mode) hn

theorem normalized_1759 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6755 (c3_mode r1_mode : Int) : ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_6756 (c3_mode r1_mode : Int) : ((r1_mode ≥ c3_mode) ↔ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (iff_congr (normalization_6750 c3_mode r1_mode) (normalization_6755 c3_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_4926 (c3_mode r1_mode : Int) : ((r1_mode ≥ c3_mode) ↔ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1759 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6756 c3_mode r1_mode) hn

theorem normalized_1760 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6757 (c3_mode r1_mode : Int) : (((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (and_congr (normalization_6753 c3_mode r1_mode) (normalization_6755 c3_mode r1_mode))

theorem normalization_6758 (c3_mode r1_mode : Int) : (((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ (((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Classification077_111 c3_mode r1_mode) := (iff_congr (normalization_6751 c3_mode r1_mode) (normalization_6757 c3_mode r1_mode))

-- Checked replay of monotonicity.
theorem replay_4927 (c3_mode r1_mode : Int) : (((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ (((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1760 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6754 c3_mode r1_mode) (replay_4925 c3_mode r1_mode)
  have n1 : (((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6756 c3_mode r1_mode) (replay_4926 c3_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6758 c3_mode r1_mode) hn

abbrev shared_expr_Classification077_112 (c3_mode r1_mode : Int) : Prop := ((((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))))
abbrev formula_2124 (c3_mode r1_mode : Int) : Prop := (shared_expr_Classification077_112 c3_mode r1_mode)

theorem normalized_1761 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6759 (c3_mode r1_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_6753 c3_mode r1_mode))

theorem normalization_6760 (c3_mode r1_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (not_congr (normalization_6755 c3_mode r1_mode))

theorem normalization_6761 (c3_mode r1_mode : Int) : ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))) := (or_congr (normalization_6759 c3_mode r1_mode) (normalization_6760 c3_mode r1_mode))

theorem normalization_6762 (c3_mode r1_mode : Int) : (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) := (not_congr (normalization_6761 c3_mode r1_mode))

abbrev shared_expr_Classification077_113 (c3_mode r1_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))))
theorem normalization_6763 (c3_mode r1_mode : Int) : (formula_2124 c3_mode r1_mode) ↔ (shared_expr_Classification077_113 c3_mode r1_mode) := (iff_congr (normalization_6757 c3_mode r1_mode) (normalization_6762 c3_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_4928 (c3_mode r1_mode : Int) : (formula_2124 c3_mode r1_mode) := by
  classical
  have ht := (normalized_1761 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6763 c3_mode r1_mode) hn

theorem normalized_1762 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6764 (c3_mode r1_mode : Int) : (((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification077_113 c3_mode r1_mode) := (iff_congr (normalization_6751 c3_mode r1_mode) (normalization_6762 c3_mode r1_mode))

-- Checked replay of trans.
theorem replay_4929 (c3_mode r1_mode : Int) : (((r1_mode ≤ c3_mode) ∧ (r1_mode ≥ c3_mode)) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1762 ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) (shared_expr_Classification077_113 c3_mode r1_mode))
  have n0 : (shared_expr_Classification077_111 c3_mode r1_mode) := by
    exact Iff.mp (normalization_6758 c3_mode r1_mode) (replay_4927 c3_mode r1_mode)
  have n1 : (shared_expr_Classification077_113 c3_mode r1_mode) := by
    exact Iff.mp (normalization_6763 c3_mode r1_mode) (replay_4928 c3_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6764 c3_mode r1_mode) hn

theorem normalized_1763 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6765 (c3_mode r1_mode : Int) : ((r1_mode = c3_mode) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification077_113 c3_mode r1_mode) := (iff_congr (normalization_6541 c3_mode r1_mode) (normalization_6762 c3_mode r1_mode))

-- Checked replay of trans.
theorem replay_4930 (c3_mode r1_mode : Int) : ((r1_mode = c3_mode) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1763 ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) (shared_expr_Classification077_113 c3_mode r1_mode))
  have n0 : (shared_expr_Classification077_111 c3_mode r1_mode) := by
    exact Iff.mp (normalization_6752 c3_mode r1_mode) (replay_4924 c3_mode r1_mode)
  have n1 : (shared_expr_Classification077_113 c3_mode r1_mode) := by
    exact Iff.mp (normalization_6764 c3_mode r1_mode) (replay_4929 c3_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6765 c3_mode r1_mode) hn

theorem normalized_1764 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6766 (c3_level r1_level : Int) : (r1_level ≤ c3_level) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6767 (c3_level r1_level : Int) : (r1_level ≥ c3_level) ↔ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_6768 (c3_level r1_level : Int) : ((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (and_congr (normalization_6766 c3_level r1_level) (normalization_6767 c3_level r1_level))

abbrev shared_expr_Classification077_114 (c3_level r1_level : Int) : Prop := (((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
theorem normalization_6769 (c3_level r1_level : Int) : ((r1_level = c3_level) ↔ ((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level))) ↔ (shared_expr_Classification077_114 c3_level r1_level) := (iff_congr (normalization_6542 c3_level r1_level) (normalization_6768 c3_level r1_level))

-- Checked replay of rewrite.
theorem replay_4931 (c3_level r1_level : Int) : ((r1_level = c3_level) ↔ ((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level))) := by
  classical
  have ht := (normalized_1764 ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6769 c3_level r1_level) hn

theorem normalized_1765 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6770 (c3_level r1_level : Int) : ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6771 (c3_level r1_level : Int) : ((r1_level ≤ c3_level) ↔ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_6766 c3_level r1_level) (normalization_6770 c3_level r1_level))

-- Checked replay of rewrite.
theorem replay_4932 (c3_level r1_level : Int) : ((r1_level ≤ c3_level) ↔ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1765 ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6771 c3_level r1_level) hn

theorem normalized_1766 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6772 (c3_level r1_level : Int) : ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_6773 (c3_level r1_level : Int) : ((r1_level ≥ c3_level) ↔ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (iff_congr (normalization_6767 c3_level r1_level) (normalization_6772 c3_level r1_level))

-- Checked replay of rewrite.
theorem replay_4933 (c3_level r1_level : Int) : ((r1_level ≥ c3_level) ↔ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1766 ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6773 c3_level r1_level) hn

theorem normalized_1767 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6774 (c3_level r1_level : Int) : (((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (and_congr (normalization_6770 c3_level r1_level) (normalization_6772 c3_level r1_level))

theorem normalization_6775 (c3_level r1_level : Int) : (((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ (((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ (shared_expr_Classification077_114 c3_level r1_level) := (iff_congr (normalization_6768 c3_level r1_level) (normalization_6774 c3_level r1_level))

-- Checked replay of monotonicity.
theorem replay_4934 (c3_level r1_level : Int) : (((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ (((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1767 ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6771 c3_level r1_level) (replay_4932 c3_level r1_level)
  have n1 : (((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6773 c3_level r1_level) (replay_4933 c3_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6775 c3_level r1_level) hn

abbrev shared_expr_Classification077_115 (c3_level r1_level : Int) : Prop := ((((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))))
abbrev formula_2125 (c3_level r1_level : Int) : Prop := (shared_expr_Classification077_115 c3_level r1_level)

theorem normalized_1768 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6776 (c3_level r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_6770 c3_level r1_level))

theorem normalization_6777 (c3_level r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_6772 c3_level r1_level))

theorem normalization_6778 (c3_level r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) := (or_congr (normalization_6776 c3_level r1_level) (normalization_6777 c3_level r1_level))

theorem normalization_6779 (c3_level r1_level : Int) : (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) := (not_congr (normalization_6778 c3_level r1_level))

abbrev shared_expr_Classification077_116 (c3_level r1_level : Int) : Prop := (((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))))
theorem normalization_6780 (c3_level r1_level : Int) : (formula_2125 c3_level r1_level) ↔ (shared_expr_Classification077_116 c3_level r1_level) := (iff_congr (normalization_6774 c3_level r1_level) (normalization_6779 c3_level r1_level))

-- Checked replay of rewrite.
theorem replay_4935 (c3_level r1_level : Int) : (formula_2125 c3_level r1_level) := by
  classical
  have ht := (normalized_1768 ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6780 c3_level r1_level) hn

theorem normalized_1769 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6781 (c3_level r1_level : Int) : (((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification077_116 c3_level r1_level) := (iff_congr (normalization_6768 c3_level r1_level) (normalization_6779 c3_level r1_level))

-- Checked replay of trans.
theorem replay_4936 (c3_level r1_level : Int) : (((r1_level ≤ c3_level) ∧ (r1_level ≥ c3_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1769 ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) (shared_expr_Classification077_116 c3_level r1_level))
  have n0 : (shared_expr_Classification077_114 c3_level r1_level) := by
    exact Iff.mp (normalization_6775 c3_level r1_level) (replay_4934 c3_level r1_level)
  have n1 : (shared_expr_Classification077_116 c3_level r1_level) := by
    exact Iff.mp (normalization_6780 c3_level r1_level) (replay_4935 c3_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6781 c3_level r1_level) hn

theorem normalized_1770 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6782 (c3_level r1_level : Int) : ((r1_level = c3_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification077_116 c3_level r1_level) := (iff_congr (normalization_6542 c3_level r1_level) (normalization_6779 c3_level r1_level))

-- Checked replay of trans.
theorem replay_4937 (c3_level r1_level : Int) : ((r1_level = c3_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1770 ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) (shared_expr_Classification077_116 c3_level r1_level))
  have n0 : (shared_expr_Classification077_114 c3_level r1_level) := by
    exact Iff.mp (normalization_6769 c3_level r1_level) (replay_4931 c3_level r1_level)
  have n1 : (shared_expr_Classification077_116 c3_level r1_level) := by
    exact Iff.mp (normalization_6781 c3_level r1_level) (replay_4936 c3_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6782 c3_level r1_level) hn

theorem normalized_1771 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6783 (c3_group r1_group : Int) : (r1_group ≤ c3_group) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6784 (c3_group r1_group : Int) : (r1_group ≥ c3_group) ↔ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_6785 (c3_group r1_group : Int) : ((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (and_congr (normalization_6783 c3_group r1_group) (normalization_6784 c3_group r1_group))

abbrev shared_expr_Classification077_117 (c3_group r1_group : Int) : Prop := (((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
theorem normalization_6786 (c3_group r1_group : Int) : ((r1_group = c3_group) ↔ ((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group))) ↔ (shared_expr_Classification077_117 c3_group r1_group) := (iff_congr (normalization_6628 c3_group r1_group) (normalization_6785 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_4938 (c3_group r1_group : Int) : ((r1_group = c3_group) ↔ ((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group))) := by
  classical
  have ht := (normalized_1771 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6786 c3_group r1_group) hn

theorem normalized_1772 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6787 (c3_group r1_group : Int) : ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6788 (c3_group r1_group : Int) : ((r1_group ≤ c3_group) ↔ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_6783 c3_group r1_group) (normalization_6787 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_4939 (c3_group r1_group : Int) : ((r1_group ≤ c3_group) ↔ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1772 ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6788 c3_group r1_group) hn

theorem normalized_1773 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6789 (c3_group r1_group : Int) : ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_6790 (c3_group r1_group : Int) : ((r1_group ≥ c3_group) ↔ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (iff_congr (normalization_6784 c3_group r1_group) (normalization_6789 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_4940 (c3_group r1_group : Int) : ((r1_group ≥ c3_group) ↔ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1773 ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6790 c3_group r1_group) hn

theorem normalized_1774 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6791 (c3_group r1_group : Int) : (((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (and_congr (normalization_6787 c3_group r1_group) (normalization_6789 c3_group r1_group))

theorem normalization_6792 (c3_group r1_group : Int) : (((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ (((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ↔ (shared_expr_Classification077_117 c3_group r1_group) := (iff_congr (normalization_6785 c3_group r1_group) (normalization_6791 c3_group r1_group))

-- Checked replay of monotonicity.
theorem replay_4941 (c3_group r1_group : Int) : (((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ (((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1774 ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6788 c3_group r1_group) (replay_4939 c3_group r1_group)
  have n1 : (((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6790 c3_group r1_group) (replay_4940 c3_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6792 c3_group r1_group) hn

abbrev shared_expr_Classification077_118 (c3_group r1_group : Int) : Prop := ((((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))
abbrev formula_2126 (c3_group r1_group : Int) : Prop := (shared_expr_Classification077_118 c3_group r1_group)

theorem normalized_1775 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6793 (c3_group r1_group : Int) : (¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_6787 c3_group r1_group))

theorem normalization_6794 (c3_group r1_group : Int) : (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (not_congr (normalization_6789 c3_group r1_group))

theorem normalization_6795 (c3_group r1_group : Int) : ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) := (or_congr (normalization_6793 c3_group r1_group) (normalization_6794 c3_group r1_group))

theorem normalization_6796 (c3_group r1_group : Int) : (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))) := (not_congr (normalization_6795 c3_group r1_group))

abbrev shared_expr_Classification077_119 (c3_group r1_group : Int) : Prop := (((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_6797 (c3_group r1_group : Int) : (formula_2126 c3_group r1_group) ↔ (shared_expr_Classification077_119 c3_group r1_group) := (iff_congr (normalization_6791 c3_group r1_group) (normalization_6796 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_4942 (c3_group r1_group : Int) : (formula_2126 c3_group r1_group) := by
  classical
  have ht := (normalized_1775 ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6797 c3_group r1_group) hn

theorem normalized_1776 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6798 (c3_group r1_group : Int) : (((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification077_119 c3_group r1_group) := (iff_congr (normalization_6785 c3_group r1_group) (normalization_6796 c3_group r1_group))

-- Checked replay of trans.
theorem replay_4943 (c3_group r1_group : Int) : (((r1_group ≤ c3_group) ∧ (r1_group ≥ c3_group)) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1776 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) (shared_expr_Classification077_119 c3_group r1_group))
  have n0 : (shared_expr_Classification077_117 c3_group r1_group) := by
    exact Iff.mp (normalization_6792 c3_group r1_group) (replay_4941 c3_group r1_group)
  have n1 : (shared_expr_Classification077_119 c3_group r1_group) := by
    exact Iff.mp (normalization_6797 c3_group r1_group) (replay_4942 c3_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6798 c3_group r1_group) hn

theorem normalized_1777 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6799 (c3_group r1_group : Int) : ((r1_group = c3_group) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification077_119 c3_group r1_group) := (iff_congr (normalization_6628 c3_group r1_group) (normalization_6796 c3_group r1_group))

-- Checked replay of trans.
theorem replay_4944 (c3_group r1_group : Int) : ((r1_group = c3_group) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1777 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) (shared_expr_Classification077_119 c3_group r1_group))
  have n0 : (shared_expr_Classification077_117 c3_group r1_group) := by
    exact Iff.mp (normalization_6786 c3_group r1_group) (replay_4938 c3_group r1_group)
  have n1 : (shared_expr_Classification077_119 c3_group r1_group) := by
    exact Iff.mp (normalization_6798 c3_group r1_group) (replay_4943 c3_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6799 c3_group r1_group) hn

theorem normalized_1778 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6800 (c3_group r1_group : Int) : (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))) := (not_congr (normalization_6796 c3_group r1_group))

abbrev shared_expr_Classification077_120 (c3_group r1_group : Int) : Prop := ((¬ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))))
theorem normalization_6801 (c3_group r1_group : Int) : ((¬ (r1_group = c3_group)) ↔ (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Classification077_120 c3_group r1_group) := (iff_congr (normalization_6629 c3_group r1_group) (normalization_6800 c3_group r1_group))

-- Checked replay of monotonicity.
theorem replay_4945 (c3_group r1_group : Int) : ((¬ (r1_group = c3_group)) ↔ (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1778 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification077_119 c3_group r1_group) := by
    exact Iff.mp (normalization_6799 c3_group r1_group) (replay_4944 c3_group r1_group)
  have hn := ht n0
  exact Iff.mpr (normalization_6801 c3_group r1_group) hn

abbrev shared_expr_Classification077_121 (c3_group r1_group : Int) : Prop := ((¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2127 (c3_group r1_group : Int) : Prop := (shared_expr_Classification077_121 c3_group r1_group)

theorem normalized_1779 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_122 (c3_group r1_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_6802 (c3_group r1_group : Int) : (formula_2127 c3_group r1_group) ↔ (shared_expr_Classification077_122 c3_group r1_group) := (iff_congr (normalization_6800 c3_group r1_group) (normalization_6795 c3_group r1_group))

-- Checked replay of rewrite.
theorem replay_4946 (c3_group r1_group : Int) : (formula_2127 c3_group r1_group) := by
  classical
  have ht := (normalized_1779 ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6802 c3_group r1_group) hn

theorem normalized_1780 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_123 (c3_group r1_group : Int) : Prop := ((¬ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_6803 (c3_group r1_group : Int) : ((¬ (r1_group = c3_group)) ↔ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) ↔ (shared_expr_Classification077_123 c3_group r1_group) := (iff_congr (normalization_6629 c3_group r1_group) (normalization_6795 c3_group r1_group))

-- Checked replay of trans.
theorem replay_4947 (c3_group r1_group : Int) : ((¬ (r1_group = c3_group)) ↔ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1780 ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification077_120 c3_group r1_group) := by
    exact Iff.mp (normalization_6801 c3_group r1_group) (replay_4945 c3_group r1_group)
  have n1 : (shared_expr_Classification077_122 c3_group r1_group) := by
    exact Iff.mp (normalization_6802 c3_group r1_group) (replay_4946 c3_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6803 c3_group r1_group) hn

abbrev shared_expr_Classification077_124 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ∧ ((¬ ((r1_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2128 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification077_124 c3_group c3_level c3_mode r1_group r1_level r1_mode)

theorem normalized_1781 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_125 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_6804 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (formula_2128 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (shared_expr_Classification077_125 c3_group c3_level c3_mode r1_group r1_level r1_mode) := (and_congr (normalization_6762 c3_mode r1_mode) (and_congr (normalization_6779 c3_level r1_level) (normalization_6795 c3_group r1_group)))

theorem normalization_6805 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group))) ↔ (formula_2128 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ↔ ((shared_expr_Classification077_1 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (shared_expr_Classification077_125 c3_group c3_level c3_mode r1_group r1_level r1_mode)) := (iff_congr (normalization_6630 c3_group c3_level c3_mode r1_group r1_level r1_mode) (normalization_6804 c3_group c3_level c3_mode r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_4948 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group))) ↔ (formula_2128 c3_group c3_level c3_mode r1_group r1_level r1_mode)) := by
  classical
  have ht := (normalized_1781 ((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))) ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification077_113 c3_mode r1_mode) := by
    exact Iff.mp (normalization_6765 c3_mode r1_mode) (replay_4930 c3_mode r1_mode)
  have n1 : (shared_expr_Classification077_116 c3_level r1_level) := by
    exact Iff.mp (normalization_6782 c3_level r1_level) (replay_4937 c3_level r1_level)
  have n2 : (shared_expr_Classification077_123 c3_group r1_group) := by
    exact Iff.mp (normalization_6803 c3_group r1_group) (replay_4947 c3_group r1_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6805 c3_group c3_level c3_mode r1_group r1_level r1_mode) hn

theorem normalized_1782 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification077_126 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_6806 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (formula_2034 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (shared_expr_Classification077_126 c3_group c3_level c3_mode r1_group r1_level r1_mode) := (or_congr (normalization_6759 c3_mode r1_mode) (or_congr (normalization_6760 c3_mode r1_mode) (or_congr (normalization_6776 c3_level r1_level) (or_congr (normalization_6777 c3_level r1_level) (normalization_6796 c3_group r1_group)))))

theorem normalization_6807 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (¬ (formula_2034 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ↔ (¬ (shared_expr_Classification077_126 c3_group c3_level c3_mode r1_group r1_level r1_mode)) := (not_congr (normalization_6806 c3_group c3_level c3_mode r1_group r1_level r1_mode))

theorem normalization_6808 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : ((formula_2128 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (formula_2034 c3_group c3_level c3_mode r1_group r1_level r1_mode))) ↔ ((shared_expr_Classification077_125 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Classification077_126 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := (iff_congr (normalization_6804 c3_group c3_level c3_mode r1_group r1_level r1_mode) (normalization_6807 c3_group c3_level c3_mode r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_4949 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : ((formula_2128 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (formula_2034 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := by
  classical
  have ht := (normalized_1782 ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6808 c3_group c3_level c3_mode r1_group r1_level r1_mode) hn

end H4Formal.Generated.Classification
