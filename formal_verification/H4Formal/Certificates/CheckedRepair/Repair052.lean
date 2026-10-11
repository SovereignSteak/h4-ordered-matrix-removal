import H4Formal.Certificates.CheckedRepair.Repair051

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_2910 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) (i183 : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)) : (formula_1464 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact Iff.mp (replay_2909 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) i183

abbrev shared_expr_Repair052_0 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((formula_1464 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (formula_1464 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
abbrev formula_1466 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_0 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

theorem normalized_1222 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair052_1 (c0_group c0_mode c1_group c1_mode : Int) : Prop := (((((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair052_2 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair052_1 c0_group c0_mode c1_group c1_mode)) ∨ ((¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair052_3 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair052_2 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair052_4 (c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
abbrev shared_expr_Repair052_5 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair052_6 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Repair052_5 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair052_7 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair052_8 (c0_node c0_sign c1_node : Int) : Prop := ((((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_7 c0_node c1_node))
abbrev shared_expr_Repair052_9 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair052_10 (c0_node c1_node c1_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair052_9 c0_node c1_node))
abbrev shared_expr_Repair052_11 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair052_10 c0_node c1_node c1_sign)))
abbrev shared_expr_Repair052_12 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair052_8 c0_node c0_sign c1_node)) ∨ (shared_expr_Repair052_11 c0_depth c0_node c1_depth c1_node c1_sign))
abbrev shared_expr_Repair052_13 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair052_6 c0_node c0_sign c1_node c1_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair052_12 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev shared_expr_Repair052_14 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair052_13 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev shared_expr_Repair052_15 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair052_14 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
abbrev shared_expr_Repair052_16 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair052_15 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
abbrev shared_expr_Repair052_17 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((shared_expr_Repair052_4 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Repair052_16 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) ↔ ((shared_expr_Repair052_4 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Repair052_16 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_5170 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1466 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Repair052_17 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (iff_congr (normalization_5168 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (normalization_5168 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2911 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1466 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  classical
  have ht := (normalized_1222 ((shared_expr_Repair052_4 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Repair052_16 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
  have hn := ht
  exact Iff.mpr (normalization_5170 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) hn

-- Checked replay of mp.
theorem replay_2912 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) (i183 : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)) : (formula_1464 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact Iff.mp (replay_2911 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (replay_2910 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign i183)

abbrev shared_expr_Repair052_18 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((c0_level = c1_level) ∧ (((c0_mode = c1_mode) ∧ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) ∨ ((¬ (c0_level = c1_level)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))
abbrev formula_1467 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (shared_expr_Repair052_18 c0_group c0_level c0_mode c1_group c1_level c1_mode)

abbrev shared_expr_Repair052_19 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_1467 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))
abbrev formula_1468 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((¬ (c1_kind = (0 : Int))) ∨ (shared_expr_Repair052_19 c0_group c0_level c0_mode c1_group c1_level c1_mode))

abbrev shared_expr_Repair052_20 (c0_node c0_sign c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ∧ (c0_sign = (0 : Int))) ∨ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))))
abbrev formula_1469 (c0_node c0_sign c1_node : Int) : Prop := (shared_expr_Repair052_20 c0_node c0_sign c1_node)

abbrev shared_expr_Repair052_21 (c0_node c1_node c1_sign : Int) : Prop := ((((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ∧ (c1_sign = (1 : Int))) ∨ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_1470 (c0_node c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_21 c0_node c1_node c1_sign)

abbrev shared_expr_Repair052_22 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ∧ (formula_1469 c0_node c0_sign c1_node)) ∨ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ∨ (formula_1470 c0_node c1_node c1_sign))))
abbrev formula_1471 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_22 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Repair052_23 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((c0_depth = c1_depth) ∧ (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) ∨ ((¬ (c0_depth = c1_depth)) ∧ (formula_1471 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev formula_1472 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_23 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Repair052_24 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (c1_kind = (0 : Int))) ∧ (((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1472 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev formula_1473 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_24 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Repair052_25 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ (formula_1468 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (formula_1473 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
abbrev formula_1474 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_25 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

abbrev shared_expr_Repair052_26 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((formula_1464 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (formula_1474 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
abbrev formula_1475 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_26 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

theorem normalized_1223 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ ((¬ p10) ∧ p11)) ∨ p12))))))))))) ↔ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ (p11 ∧ (¬ p10))) ∨ p12)))))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5171 (c0_group c1_group : Int) : ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)) ↔ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5172 (c0_group c1_group : Int) : (¬ ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_5171 c0_group c1_group))

theorem normalization_5173 (c0_mode c1_mode : Int) : ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) ↔ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5174 (c0_mode c1_mode : Int) : (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_5173 c0_mode c1_mode))

theorem normalization_5175 (c0_group c0_mode c1_group c1_mode : Int) : (((c0_mode = c1_mode) ∧ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))) ↔ (shared_expr_Repair052_1 c0_group c0_mode c1_group c1_mode) := (or_congr (and_congr (normalization_5138 c0_mode c1_mode) (normalization_5172 c0_group c1_group)) (and_congr (not_congr (normalization_5138 c0_mode c1_mode)) (normalization_5174 c0_mode c1_mode)))

theorem normalization_5176 (c0_level c1_level : Int) : ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ↔ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5177 (c0_level c1_level : Int) : (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5176 c0_level c1_level))

theorem normalization_5178 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1467 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Repair052_2 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_5137 c0_level c1_level) (normalization_5175 c0_group c0_mode c1_group c1_mode)) (and_congr (not_congr (normalization_5137 c0_level c1_level)) (normalization_5177 c0_level c1_level)))

theorem normalization_5179 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (shared_expr_Repair052_19 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_5136 c0_mode c1_mode) (normalization_5178 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (and_congr (not_congr (normalization_5136 c0_mode c1_mode)) (normalization_693 c0_mode)))

theorem normalization_5180 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (formula_1468 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (or_congr (normalization_5135 c1_kind) (normalization_5179 c0_group c0_level c0_mode c1_group c1_level c1_mode))

theorem normalization_5181 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5182 (c0_node c1_node : Int) : (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5181 c0_node c1_node))

theorem normalization_5183 (c0_node c0_sign c1_node c1_sign : Int) : (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ↔ (shared_expr_Repair052_6 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_5116 c0_node c1_node) (normalization_5117 c0_sign c1_sign)) (and_congr (not_congr (normalization_5116 c0_node c1_node)) (normalization_5182 c0_node c1_node)))

theorem normalization_5184 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_5185 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_5186 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5187 (c0_node c1_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (not_congr (normalization_5186 c0_node c1_node))

theorem normalization_5188 (c0_node c0_sign c1_node : Int) : (formula_1469 c0_node c0_sign c1_node) ↔ (shared_expr_Repair052_8 c0_node c0_sign c1_node) := (or_congr (and_congr (normalization_5185 c0_node c1_node) (normalization_144 c0_sign)) (and_congr (not_congr (normalization_5185 c0_node c1_node)) (normalization_5187 c0_node c1_node)))

theorem normalization_5189 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) := by
  omega

theorem normalization_5190 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ↔ (¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) := (not_congr (normalization_5189 c0_depth c1_depth))

theorem normalization_5191 (c0_node c1_node : Int) : ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_5192 (c0_node c1_node : Int) : ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5193 (c0_node c1_node : Int) : (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5192 c0_node c1_node))

theorem normalization_5194 (c0_node c1_node c1_sign : Int) : (formula_1470 c0_node c1_node c1_sign) ↔ (shared_expr_Repair052_10 c0_node c1_node c1_sign) := (or_congr (and_congr (normalization_5191 c0_node c1_node) (normalization_1456 c1_sign)) (and_congr (not_congr (normalization_5191 c0_node c1_node)) (normalization_5193 c0_node c1_node)))

theorem normalization_5195 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ∨ (formula_1470 c0_node c1_node c1_sign)) ↔ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair052_10 c0_node c1_node c1_sign)) := (or_congr (normalization_5190 c0_depth c1_depth) (normalization_5194 c0_node c1_node c1_sign))

abbrev shared_expr_Repair052_27 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair052_10 c0_node c1_node c1_sign)))
abbrev shared_expr_Repair052_28 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair052_8 c0_node c0_sign c1_node)) ∨ (shared_expr_Repair052_27 c0_depth c0_node c1_depth c1_node c1_sign))
theorem normalization_5196 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1471 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Repair052_28 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5184 c0_depth c1_depth) (normalization_5188 c0_node c0_sign c1_node)) (and_congr (not_congr (normalization_5184 c0_depth c1_depth)) (normalization_5195 c0_depth c0_node c1_depth c1_node c1_sign)))

abbrev shared_expr_Repair052_29 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair052_6 c0_node c0_sign c1_node c1_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair052_28 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
theorem normalization_5197 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1472 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Repair052_29 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5115 c0_depth c1_depth) (normalization_5183 c0_node c0_sign c1_node c1_sign)) (and_congr (not_congr (normalization_5115 c0_depth c1_depth)) (normalization_5196 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

theorem normalization_5198 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : ((¬ (c1_kind = (2 : Int))) ∧ (formula_1472 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair052_29 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (and_congr (normalization_5149 c1_kind) (normalization_5197 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

abbrev shared_expr_Repair052_30 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair052_29 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev shared_expr_Repair052_31 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair052_30 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_5199 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1472 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))) ↔ (shared_expr_Repair052_31 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_141 c0_kind) (normalization_1447 c1_kind)) (and_congr (not_congr (normalization_141 c0_kind)) (normalization_5198 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

theorem normalization_5200 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1473 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair052_31 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) := (and_congr (normalization_5135 c1_kind) (normalization_5199 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

abbrev shared_expr_Repair052_32 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair052_31 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_5201 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1474 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ ((shared_expr_Repair052_4 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Repair052_32 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) := (or_congr (and_congr (normalization_134 c0_kind) (normalization_5180 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (and_congr (not_congr (normalization_134 c0_kind)) (normalization_5200 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Repair052_33 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((shared_expr_Repair052_4 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Repair052_16 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) ↔ ((shared_expr_Repair052_4 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Repair052_32 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_5202 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1475 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Repair052_33 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (iff_congr (normalization_5168 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (normalization_5201 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2913 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1475 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  classical
  have ht := (normalized_1223 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) (shared_expr_Repair052_6 c0_node c0_sign c1_node c1_sign) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) (shared_expr_Repair052_8 c0_node c0_sign c1_node) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) (shared_expr_Repair052_10 c0_node c1_node c1_sign))
  have hn := ht
  exact Iff.mpr (normalization_5202 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) hn

-- Checked replay of mp.
theorem replay_2914 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) (i183 : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)) : (formula_1474 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact Iff.mp (replay_2913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (replay_2912 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign i183)

theorem normalized_1224 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5203 (c1_kind : Int) : (¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := (not_congr (normalization_1683 c1_kind))

theorem normalization_5204 (c1_kind : Int) : ((¬ (c1_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))))) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))))) := (iff_congr (normalization_5135 c1_kind) (normalization_5203 c1_kind))

-- Checked replay of monotonicity.
theorem replay_2915 (c1_kind : Int) : ((¬ (c1_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1224 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1685 c1_kind) (replay_319 c1_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_5204 c1_kind) hn

theorem normalized_1225 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5205 (c1_kind : Int) : ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ↔ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ↔ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_5203 c1_kind) (normalization_1682 c1_kind))

-- Checked replay of rewrite.
theorem replay_2916 (c1_kind : Int) : ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ↔ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1225 ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_5205 c1_kind) hn

theorem normalized_1226 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5206 (c1_kind : Int) : ((¬ (c1_kind = (0 : Int))) ↔ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_5135 c1_kind) (normalization_1682 c1_kind))

-- Checked replay of trans.
theorem replay_2917 (c1_kind : Int) : ((¬ (c1_kind = (0 : Int))) ↔ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1226 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))
  have n0 : ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))))) := by
    exact Iff.mp (normalization_5204 c1_kind) (replay_2915 c1_kind)
  have n1 : ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_5205 c1_kind) (replay_2916 c1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5206 c1_kind) hn

abbrev shared_expr_Repair052_34 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((shared_expr_Repair052_19 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_1476 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (shared_expr_Repair052_34 c0_group c0_level c0_mode c1_group c1_level c1_mode)

theorem normalized_1227 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5207 (c0_level c1_level : Int) : ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5208 (c0_level c1_level : Int) : (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) := (not_congr (normalization_5207 c0_level c1_level))

theorem normalization_5209 (c0_level c1_level : Int) : ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ↔ ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) := (or_congr (normalization_5208 c0_level c1_level) (normalization_5177 c0_level c1_level))

theorem normalization_5210 (c0_mode c1_mode : Int) : ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_5211 (c0_mode c1_mode : Int) : (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) := (not_congr (normalization_5210 c0_mode c1_mode))

theorem normalization_5212 (c0_mode c1_mode : Int) : ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_5211 c0_mode c1_mode) (normalization_5174 c0_mode c1_mode))

abbrev shared_expr_Repair052_35 (c0_group c0_mode c1_group c1_mode : Int) : Prop := ((((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))))))
theorem normalization_5213 (c0_group c0_mode c1_group c1_mode : Int) : (formula_651 c0_group c0_mode c1_group c1_mode) ↔ (shared_expr_Repair052_35 c0_group c0_mode c1_group c1_mode) := (or_congr (and_congr (normalization_5212 c0_mode c1_mode) (normalization_5174 c0_mode c1_mode)) (and_congr (not_congr (normalization_5212 c0_mode c1_mode)) (normalization_5172 c0_group c1_group)))

abbrev shared_expr_Repair052_36 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair052_35 c0_group c0_mode c1_group c1_mode)))
theorem normalization_5214 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Repair052_36 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_5209 c0_level c1_level) (normalization_5177 c0_level c1_level)) (and_congr (not_congr (normalization_5209 c0_level c1_level)) (normalization_5213 c0_group c0_mode c1_group c1_mode)))

abbrev shared_expr_Repair052_37 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair052_36 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_5215 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))) ↔ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_5136 c0_mode c1_mode) (normalization_5214 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (and_congr (not_congr (normalization_5136 c0_mode c1_mode)) (normalization_693 c0_mode)))

theorem normalization_5216 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1476 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ ((shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (iff_congr (normalization_5179 c0_group c0_level c0_mode c1_group c1_level c1_mode) (normalization_5215 c0_group c0_level c0_mode c1_group c1_level c1_mode))

-- Checked replay of rewrite.
theorem replay_2918 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1476 c0_group c0_level c0_mode c1_group c1_level c1_mode) := by
  classical
  have ht := (normalized_1227 ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)) ((c0_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5216 c0_group c0_level c0_mode c1_group c1_level c1_mode) hn

abbrev shared_expr_Repair052_38 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_1477 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (shared_expr_Repair052_38 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)

theorem normalized_1228 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5217 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (formula_1477 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (or_congr (normalization_1682 c1_kind) (normalization_5215 c0_group c0_level c0_mode c1_group c1_level c1_mode))

abbrev shared_expr_Repair052_39 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ↔ (((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
theorem normalization_5218 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1468 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1477 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ↔ (shared_expr_Repair052_39 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := (iff_congr (normalization_5180 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (normalization_5217 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode))

-- Checked replay of monotonicity.
theorem replay_2919 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1468 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1477 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) := by
  classical
  have ht := (normalized_1228 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode) (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode))
  have n0 : ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_5206 c1_kind) (replay_2917 c1_kind)
  have n1 : ((shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := by
    exact Iff.mp (normalization_5216 c0_group c0_level c0_mode c1_group c1_level c1_mode) (replay_2918 c0_group c0_level c0_mode c1_group c1_level c1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5218 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) hn

theorem normalized_1229 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5219 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (or_congr (normalization_1680 c1_kind) (or_congr (normalization_1681 c1_kind) (normalization_5215 c0_group c0_level c0_mode c1_group c1_level c1_mode)))

abbrev shared_expr_Repair052_40 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
theorem normalization_5220 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1477 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ↔ (shared_expr_Repair052_40 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := (iff_congr (normalization_5217 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (normalization_5219 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode))

-- Checked replay of rewrite.
theorem replay_2920 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1477 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) := by
  classical
  have ht := (normalized_1229 ((c1_kind) ≤ (0 : Int)) ((c1_kind) ≤ (-1 : Int)) (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode))
  have hn := ht
  exact Iff.mpr (normalization_5220 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) hn

theorem normalized_1230 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair052_41 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
theorem normalization_5221 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1468 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ↔ (shared_expr_Repair052_41 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := (iff_congr (normalization_5180 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (normalization_5219 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode))

-- Checked replay of trans.
theorem replay_2921 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1468 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) := by
  classical
  have ht := (normalized_1230 ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_3 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair052_37 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
  have n0 : (shared_expr_Repair052_39 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := by
    exact Iff.mp (normalization_5218 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (replay_2919 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)
  have n1 : (shared_expr_Repair052_40 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := by
    exact Iff.mp (normalization_5220 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (replay_2920 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5221 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) hn

theorem normalized_1231 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5222 (c1_kind : Int) : (¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := (not_congr (normalization_1774 c1_kind))

theorem normalization_5223 (c1_kind : Int) : ((¬ (c1_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))))) ↔ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))) := (iff_congr (normalization_5149 c1_kind) (normalization_5222 c1_kind))

-- Checked replay of monotonicity.
theorem replay_2922 (c1_kind : Int) : ((¬ (c1_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_1231 (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))
  have n0 : ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1776 c1_kind) (replay_355 c1_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_5223 c1_kind) hn

theorem normalized_1232 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5224 (c1_kind : Int) : ((¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ↔ ((¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_5222 c1_kind) (normalization_1773 c1_kind))

-- Checked replay of rewrite.
theorem replay_2923 (c1_kind : Int) : ((¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_1232 ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_5224 c1_kind) hn

theorem normalized_1233 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5225 (c1_kind : Int) : ((¬ (c1_kind = (2 : Int))) ↔ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ↔ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ↔ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_5149 c1_kind) (normalization_1773 c1_kind))

-- Checked replay of trans.
theorem replay_2924 (c1_kind : Int) : ((¬ (c1_kind = (2 : Int))) ↔ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_1233 (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))
  have n0 : ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_5223 c1_kind) (replay_2922 c1_kind)
  have n1 : ((¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_5224 c1_kind) (replay_2923 c1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5225 c1_kind) hn

theorem normalized_1234 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5226 (c0_depth c1_depth : Int) : (c0_depth ≤ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_5227 (c0_depth c1_depth : Int) : (c0_depth ≥ c1_depth) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5228 (c0_depth c1_depth : Int) : ((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_5226 c0_depth c1_depth) (normalization_5227 c0_depth c1_depth))

abbrev shared_expr_Repair052_42 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))
theorem normalization_5229 (c0_depth c1_depth : Int) : ((c0_depth = c1_depth) ↔ ((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth))) ↔ (shared_expr_Repair052_42 c0_depth c1_depth) := (iff_congr (normalization_5115 c0_depth c1_depth) (normalization_5228 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2925 (c0_depth c1_depth : Int) : ((c0_depth = c1_depth) ↔ ((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth))) := by
  classical
  have ht := (normalized_1234 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5229 c0_depth c1_depth) hn

theorem normalized_1235 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5230 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_5231 (c0_depth c1_depth : Int) : ((c0_depth ≤ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := (iff_congr (normalization_5226 c0_depth c1_depth) (normalization_5230 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2926 (c0_depth c1_depth : Int) : ((c0_depth ≤ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1235 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5231 c0_depth c1_depth) hn

theorem normalized_1236 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5232 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5233 (c0_depth c1_depth : Int) : ((c0_depth ≥ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_5227 c0_depth c1_depth) (normalization_5232 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2927 (c0_depth c1_depth : Int) : ((c0_depth ≥ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1236 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5233 c0_depth c1_depth) hn

theorem normalized_1237 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5234 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_5230 c0_depth c1_depth) (normalization_5232 c0_depth c1_depth))

theorem normalization_5235 (c0_depth c1_depth : Int) : (((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Repair052_42 c0_depth c1_depth) := (iff_congr (normalization_5228 c0_depth c1_depth) (normalization_5234 c0_depth c1_depth))

-- Checked replay of monotonicity.
theorem replay_2928 (c0_depth c1_depth : Int) : (((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1237 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))
  have n0 : (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5231 c0_depth c1_depth) (replay_2926 c0_depth c1_depth)
  have n1 : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5233 c0_depth c1_depth) (replay_2927 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5235 c0_depth c1_depth) hn

abbrev shared_expr_Repair052_43 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))))
abbrev formula_1478 (c0_depth c1_depth : Int) : Prop := (shared_expr_Repair052_43 c0_depth c1_depth)

theorem normalized_1238 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5236 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := (not_congr (normalization_5230 c0_depth c1_depth))

theorem normalization_5237 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_5232 c0_depth c1_depth))

theorem normalization_5238 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_5236 c0_depth c1_depth) (normalization_5237 c0_depth c1_depth))

theorem normalization_5239 (c0_depth c1_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_5238 c0_depth c1_depth))

abbrev shared_expr_Repair052_44 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))))
theorem normalization_5240 (c0_depth c1_depth : Int) : (formula_1478 c0_depth c1_depth) ↔ (shared_expr_Repair052_44 c0_depth c1_depth) := (iff_congr (normalization_5234 c0_depth c1_depth) (normalization_5239 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2929 (c0_depth c1_depth : Int) : (formula_1478 c0_depth c1_depth) := by
  classical
  have ht := (normalized_1238 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5240 c0_depth c1_depth) hn

theorem normalized_1239 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5241 (c0_depth c1_depth : Int) : (((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair052_44 c0_depth c1_depth) := (iff_congr (normalization_5228 c0_depth c1_depth) (normalization_5239 c0_depth c1_depth))

-- Checked replay of trans.
theorem replay_2930 (c0_depth c1_depth : Int) : (((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1239 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) (shared_expr_Repair052_44 c0_depth c1_depth))
  have n0 : (shared_expr_Repair052_42 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5235 c0_depth c1_depth) (replay_2928 c0_depth c1_depth)
  have n1 : (shared_expr_Repair052_44 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5240 c0_depth c1_depth) (replay_2929 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5241 c0_depth c1_depth) hn

theorem normalized_1240 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5242 (c0_depth c1_depth : Int) : ((c0_depth = c1_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair052_44 c0_depth c1_depth) := (iff_congr (normalization_5115 c0_depth c1_depth) (normalization_5239 c0_depth c1_depth))

-- Checked replay of trans.
theorem replay_2931 (c0_depth c1_depth : Int) : ((c0_depth = c1_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1240 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) (shared_expr_Repair052_44 c0_depth c1_depth))
  have n0 : (shared_expr_Repair052_42 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5229 c0_depth c1_depth) (replay_2925 c0_depth c1_depth)
  have n1 : (shared_expr_Repair052_44 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5241 c0_depth c1_depth) (replay_2930 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5242 c0_depth c1_depth) hn

theorem normalized_1241 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5243 (c0_node c1_node : Int) : (c0_node ≤ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5244 (c0_node c1_node : Int) : (c0_node ≥ c1_node) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5245 (c0_node c1_node : Int) : ((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_5243 c0_node c1_node) (normalization_5244 c0_node c1_node))

abbrev shared_expr_Repair052_45 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
theorem normalization_5246 (c0_node c1_node : Int) : ((c0_node = c1_node) ↔ ((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node))) ↔ (shared_expr_Repair052_45 c0_node c1_node) := (iff_congr (normalization_5116 c0_node c1_node) (normalization_5245 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2932 (c0_node c1_node : Int) : ((c0_node = c1_node) ↔ ((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node))) := by
  classical
  have ht := (normalized_1241 (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5246 c0_node c1_node) hn

theorem normalized_1242 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5247 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5248 (c0_node c1_node : Int) : ((c0_node ≤ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (iff_congr (normalization_5243 c0_node c1_node) (normalization_5247 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2933 (c0_node c1_node : Int) : ((c0_node ≤ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1242 ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5248 c0_node c1_node) hn

theorem normalized_1243 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5249 (c0_node c1_node : Int) : ((c0_node ≥ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_5244 c0_node c1_node) (normalization_5181 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2934 (c0_node c1_node : Int) : ((c0_node ≥ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1243 ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5249 c0_node c1_node) hn

theorem normalized_1244 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5250 (c0_node c1_node : Int) : (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_5247 c0_node c1_node) (normalization_5181 c0_node c1_node))

theorem normalization_5251 (c0_node c1_node : Int) : (((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair052_45 c0_node c1_node) := (iff_congr (normalization_5245 c0_node c1_node) (normalization_5250 c0_node c1_node))

-- Checked replay of monotonicity.
theorem replay_2935 (c0_node c1_node : Int) : (((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1244 ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
  have n0 : (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5248 c0_node c1_node) (replay_2933 c0_node c1_node)
  have n1 : ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5249 c0_node c1_node) (replay_2934 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5251 c0_node c1_node) hn

abbrev shared_expr_Repair052_46 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))))
abbrev formula_1479 (c0_node c1_node : Int) : Prop := (shared_expr_Repair052_46 c0_node c1_node)

theorem normalized_1245 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5252 (c0_node c1_node : Int) : (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (not_congr (normalization_5247 c0_node c1_node))

theorem normalization_5253 (c0_node c1_node : Int) : ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ↔ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) := (or_congr (normalization_5252 c0_node c1_node) (normalization_5182 c0_node c1_node))

theorem normalization_5254 (c0_node c1_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_5253 c0_node c1_node))

abbrev shared_expr_Repair052_47 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))))
theorem normalization_5255 (c0_node c1_node : Int) : (formula_1479 c0_node c1_node) ↔ (shared_expr_Repair052_47 c0_node c1_node) := (iff_congr (normalization_5250 c0_node c1_node) (normalization_5254 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2936 (c0_node c1_node : Int) : (formula_1479 c0_node c1_node) := by
  classical
  have ht := (normalized_1245 ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5255 c0_node c1_node) hn

theorem normalized_1246 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5256 (c0_node c1_node : Int) : (((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair052_47 c0_node c1_node) := (iff_congr (normalization_5245 c0_node c1_node) (normalization_5254 c0_node c1_node))

-- Checked replay of trans.
theorem replay_2937 (c0_node c1_node : Int) : (((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1246 (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) (shared_expr_Repair052_47 c0_node c1_node))
  have n0 : (shared_expr_Repair052_45 c0_node c1_node) := by
    exact Iff.mp (normalization_5251 c0_node c1_node) (replay_2935 c0_node c1_node)
  have n1 : (shared_expr_Repair052_47 c0_node c1_node) := by
    exact Iff.mp (normalization_5255 c0_node c1_node) (replay_2936 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5256 c0_node c1_node) hn

theorem normalized_1247 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5257 (c0_node c1_node : Int) : ((c0_node = c1_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair052_47 c0_node c1_node) := (iff_congr (normalization_5116 c0_node c1_node) (normalization_5254 c0_node c1_node))

-- Checked replay of trans.
theorem replay_2938 (c0_node c1_node : Int) : ((c0_node = c1_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1247 (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) (shared_expr_Repair052_47 c0_node c1_node))
  have n0 : (shared_expr_Repair052_45 c0_node c1_node) := by
    exact Iff.mp (normalization_5246 c0_node c1_node) (replay_2932 c0_node c1_node)
  have n1 : (shared_expr_Repair052_47 c0_node c1_node) := by
    exact Iff.mp (normalization_5256 c0_node c1_node) (replay_2937 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5257 c0_node c1_node) hn

theorem normalized_1248 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5258 (c1_sign : Int) : ((c1_sign ≤ (1 : Int)) ∧ (c1_sign ≥ (1 : Int))) ↔ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) := (and_congr (normalization_1840 c1_sign) (normalization_1842 c1_sign))

theorem normalization_5259 (c1_sign : Int) : ((c1_sign = (1 : Int)) ↔ ((c1_sign ≤ (1 : Int)) ∧ (c1_sign ≥ (1 : Int)))) ↔ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) := (iff_congr (normalization_1456 c1_sign) (normalization_5258 c1_sign))

-- Checked replay of rewrite.
theorem replay_2939 (c1_sign : Int) : ((c1_sign = (1 : Int)) ↔ ((c1_sign ≤ (1 : Int)) ∧ (c1_sign ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1248 (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5259 c1_sign) hn

theorem normalized_1249 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5260 (c1_sign : Int) : (((c1_sign ≤ (1 : Int)) ∧ (c1_sign ≥ (1 : Int))) ↔ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) ↔ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_5258 c1_sign) (normalization_1845 c1_sign))

-- Checked replay of rewrite.
theorem replay_2940 (c1_sign : Int) : (((c1_sign ≤ (1 : Int)) ∧ (c1_sign ≥ (1 : Int))) ↔ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1249 ((c1_sign) ≤ (1 : Int)) ((c1_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5260 c1_sign) hn

theorem normalized_1250 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5261 (c1_sign : Int) : ((c1_sign = (1 : Int)) ↔ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) ↔ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_1456 c1_sign) (normalization_1845 c1_sign))

-- Checked replay of trans.
theorem replay_2941 (c1_sign : Int) : ((c1_sign = (1 : Int)) ↔ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1250 (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))))
  have n0 : ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_5259 c1_sign) (replay_2939 c1_sign)
  have n1 : ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_5260 c1_sign) (replay_2940 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5261 c1_sign) hn

theorem normalized_1251 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5262 (c0_sign c1_sign : Int) : ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := (and_congr (normalization_461 c0_sign) (normalization_1845 c1_sign))

abbrev shared_expr_Repair052_48 (c0_sign c1_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))))
theorem normalization_5263 (c0_sign c1_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))) ↔ (shared_expr_Repair052_48 c0_sign c1_sign) := (iff_congr (normalization_5117 c0_sign c1_sign) (normalization_5262 c0_sign c1_sign))

-- Checked replay of monotonicity.
theorem replay_2942 (c0_sign c1_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_1251 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))
  have n0 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3117 c0_sign) (replay_2177 c0_sign)
  have n1 : ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_5261 c1_sign) (replay_2941 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5263 c0_sign c1_sign) hn

abbrev shared_expr_Repair052_49 (c0_sign c1_sign : Int) : Prop := (((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev formula_1480 (c0_sign c1_sign : Int) : Prop := (shared_expr_Repair052_49 c0_sign c1_sign)

theorem normalized_1252 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5264 (c0_sign c1_sign : Int) : ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))) ↔ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) := (or_congr (normalization_457 c0_sign) (or_congr (normalization_459 c0_sign) (or_congr (normalization_1841 c1_sign) (normalization_1843 c1_sign))))

theorem normalization_5265 (c0_sign c1_sign : Int) : (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) := (not_congr (normalization_5264 c0_sign c1_sign))

abbrev shared_expr_Repair052_50 (c0_sign c1_sign : Int) : Prop := (((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))))
theorem normalization_5266 (c0_sign c1_sign : Int) : (formula_1480 c0_sign c1_sign) ↔ (shared_expr_Repair052_50 c0_sign c1_sign) := (iff_congr (normalization_5262 c0_sign c1_sign) (normalization_5265 c0_sign c1_sign))

-- Checked replay of rewrite.
theorem replay_2943 (c0_sign c1_sign : Int) : (formula_1480 c0_sign c1_sign) := by
  classical
  have ht := (normalized_1252 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c1_sign) ≤ (1 : Int)) ((c1_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5266 c0_sign c1_sign) hn

theorem normalized_1253 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair052_51 (c0_sign c1_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))))
theorem normalization_5267 (c0_sign c1_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) ↔ (shared_expr_Repair052_51 c0_sign c1_sign) := (iff_congr (normalization_5117 c0_sign c1_sign) (normalization_5265 c0_sign c1_sign))

-- Checked replay of trans.
theorem replay_2944 (c0_sign c1_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1253 ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair052_48 c0_sign c1_sign) := by
    exact Iff.mp (normalization_5263 c0_sign c1_sign) (replay_2942 c0_sign c1_sign)
  have n1 : (shared_expr_Repair052_50 c0_sign c1_sign) := by
    exact Iff.mp (normalization_5266 c0_sign c1_sign) (replay_2943 c0_sign c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5267 c0_sign c1_sign) hn

abbrev shared_expr_Repair052_52 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair052_53 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Repair052_52 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))
abbrev formula_1481 (c0_node c0_sign c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_53 c0_node c0_sign c1_node c1_sign)

abbrev shared_expr_Repair052_54 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ↔ (formula_1481 c0_node c0_sign c1_node c1_sign))
abbrev formula_1482 (c0_node c0_sign c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_54 c0_node c0_sign c1_node c1_sign)

theorem normalized_1254 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair052_55 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair052_56 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Repair052_55 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))))
theorem normalization_5268 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1481 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Repair052_56 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_5254 c0_node c1_node) (normalization_5265 c0_sign c1_sign)) (and_congr (not_congr (normalization_5254 c0_node c1_node)) (normalization_5182 c0_node c1_node)))

theorem normalization_5269 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1482 c0_node c0_sign c1_node c1_sign) ↔ ((shared_expr_Repair052_6 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Repair052_56 c0_node c0_sign c1_node c1_sign)) := (iff_congr (normalization_5183 c0_node c0_sign c1_node c1_sign) (normalization_5268 c0_node c0_sign c1_node c1_sign))

-- Checked replay of monotonicity.
theorem replay_2945 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1482 c0_node c0_sign c1_node c1_sign) := by
  classical
  have ht := (normalized_1254 (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair052_47 c0_node c1_node) := by
    exact Iff.mp (normalization_5257 c0_node c1_node) (replay_2938 c0_node c1_node)
  have n1 : (shared_expr_Repair052_51 c0_sign c1_sign) := by
    exact Iff.mp (normalization_5267 c0_sign c1_sign) (replay_2944 c0_sign c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5269 c0_node c0_sign c1_node c1_sign) hn

theorem normalized_1255 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair052_57 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair052_55 c0_node c0_sign c1_node c1_sign))
theorem normalization_5270 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1449 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Repair052_57 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_5253 c0_node c1_node) (normalization_5182 c0_node c1_node)) (and_congr (not_congr (normalization_5253 c0_node c1_node)) (normalization_5265 c0_sign c1_sign)))

theorem normalization_5271 (c0_node c0_sign c1_node c1_sign : Int) : ((formula_1481 c0_node c0_sign c1_node c1_sign) ↔ (formula_1449 c0_node c0_sign c1_node c1_sign)) ↔ ((shared_expr_Repair052_56 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Repair052_57 c0_node c0_sign c1_node c1_sign)) := (iff_congr (normalization_5268 c0_node c0_sign c1_node c1_sign) (normalization_5270 c0_node c0_sign c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2946 (c0_node c0_sign c1_node c1_sign : Int) : ((formula_1481 c0_node c0_sign c1_node c1_sign) ↔ (formula_1449 c0_node c0_sign c1_node c1_sign)) := by
  classical
  have ht := (normalized_1255 ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5271 c0_node c0_sign c1_node c1_sign) hn

abbrev shared_expr_Repair052_58 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ↔ (formula_1449 c0_node c0_sign c1_node c1_sign))
abbrev formula_1483 (c0_node c0_sign c1_node c1_sign : Int) : Prop := (shared_expr_Repair052_58 c0_node c0_sign c1_node c1_sign)

theorem normalized_1256 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5272 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1483 c0_node c0_sign c1_node c1_sign) ↔ ((shared_expr_Repair052_6 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Repair052_57 c0_node c0_sign c1_node c1_sign)) := (iff_congr (normalization_5183 c0_node c0_sign c1_node c1_sign) (normalization_5270 c0_node c0_sign c1_node c1_sign))

-- Checked replay of trans.
theorem replay_2947 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1483 c0_node c0_sign c1_node c1_sign) := by
  classical
  have ht := (normalized_1256 (shared_expr_Repair052_6 c0_node c0_sign c1_node c1_sign) (shared_expr_Repair052_56 c0_node c0_sign c1_node c1_sign) (shared_expr_Repair052_57 c0_node c0_sign c1_node c1_sign))
  have n0 : ((shared_expr_Repair052_6 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Repair052_56 c0_node c0_sign c1_node c1_sign)) := by
    exact Iff.mp (normalization_5269 c0_node c0_sign c1_node c1_sign) (replay_2945 c0_node c0_sign c1_node c1_sign)
  have n1 : ((shared_expr_Repair052_56 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Repair052_57 c0_node c0_sign c1_node c1_sign)) := by
    exact Iff.mp (normalization_5271 c0_node c0_sign c1_node c1_sign) (replay_2946 c0_node c0_sign c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5272 c0_node c0_sign c1_node c1_sign) hn

theorem normalized_1257 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5273 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5274 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_5275 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_5273 c0_depth c1_depth) (normalization_5274 c0_depth c1_depth))

abbrev shared_expr_Repair052_59 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))
theorem normalization_5276 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Repair052_59 c0_depth c1_depth) := (iff_congr (normalization_5184 c0_depth c1_depth) (normalization_5275 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2948 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_1257 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5276 c0_depth c1_depth) hn

abbrev shared_expr_Repair052_60 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))))))
abbrev formula_1484 (c0_depth c1_depth : Int) : Prop := (shared_expr_Repair052_60 c0_depth c1_depth)

theorem normalized_1258 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5277 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) := (not_congr (normalization_5273 c0_depth c1_depth))

theorem normalization_5278 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_5274 c0_depth c1_depth))

theorem normalization_5279 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_5277 c0_depth c1_depth) (normalization_5278 c0_depth c1_depth))

theorem normalization_5280 (c0_depth c1_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_5279 c0_depth c1_depth))

abbrev shared_expr_Repair052_61 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))))
theorem normalization_5281 (c0_depth c1_depth : Int) : (formula_1484 c0_depth c1_depth) ↔ (shared_expr_Repair052_61 c0_depth c1_depth) := (iff_congr (normalization_5275 c0_depth c1_depth) (normalization_5280 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2949 (c0_depth c1_depth : Int) : (formula_1484 c0_depth c1_depth) := by
  classical
  have ht := (normalized_1258 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5281 c0_depth c1_depth) hn

theorem normalized_1259 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5282 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Repair052_61 c0_depth c1_depth) := (iff_congr (normalization_5184 c0_depth c1_depth) (normalization_5280 c0_depth c1_depth))

-- Checked replay of trans.
theorem replay_2950 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_1259 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) (shared_expr_Repair052_61 c0_depth c1_depth))
  have n0 : (shared_expr_Repair052_59 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5276 c0_depth c1_depth) (replay_2948 c0_depth c1_depth)
  have n1 : (shared_expr_Repair052_61 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5281 c0_depth c1_depth) (replay_2949 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5282 c0_depth c1_depth) hn

theorem normalized_1260 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5283 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5284 (c0_node c1_node : Int) : (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (and_congr (normalization_5283 c0_node c1_node) (normalization_5186 c0_node c1_node))

abbrev shared_expr_Repair052_62 (c0_node c1_node : Int) : Prop := (((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_5285 (c0_node c1_node : Int) : (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Repair052_62 c0_node c1_node) := (iff_congr (normalization_5185 c0_node c1_node) (normalization_5284 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2951 (c0_node c1_node : Int) : (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1260 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5285 c0_node c1_node) hn

abbrev shared_expr_Repair052_63 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1485 (c0_node c1_node : Int) : Prop := (shared_expr_Repair052_63 c0_node c1_node)

theorem normalized_1261 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5286 (c0_node c1_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5283 c0_node c1_node))

theorem normalization_5287 (c0_node c1_node : Int) : ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) := (or_congr (normalization_5286 c0_node c1_node) (normalization_5187 c0_node c1_node))

theorem normalization_5288 (c0_node c1_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) := (not_congr (normalization_5287 c0_node c1_node))

abbrev shared_expr_Repair052_64 (c0_node c1_node : Int) : Prop := (((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
theorem normalization_5289 (c0_node c1_node : Int) : (formula_1485 c0_node c1_node) ↔ (shared_expr_Repair052_64 c0_node c1_node) := (iff_congr (normalization_5284 c0_node c1_node) (normalization_5288 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2952 (c0_node c1_node : Int) : (formula_1485 c0_node c1_node) := by
  classical
  have ht := (normalized_1261 (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)) (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5289 c0_node c1_node) hn

abbrev shared_expr_Repair052_65 (c0_node c1_node : Int) : Prop := (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1486 (c0_node c1_node : Int) : Prop := (shared_expr_Repair052_65 c0_node c1_node)

theorem normalized_1262 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5290 (c0_node c1_node : Int) : (formula_1486 c0_node c1_node) ↔ (shared_expr_Repair052_64 c0_node c1_node) := (iff_congr (normalization_5185 c0_node c1_node) (normalization_5288 c0_node c1_node))

-- Checked replay of trans.
theorem replay_2953 (c0_node c1_node : Int) : (formula_1486 c0_node c1_node) := by
  classical
  have ht := (normalized_1262 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) (shared_expr_Repair052_64 c0_node c1_node))
  have n0 : (shared_expr_Repair052_62 c0_node c1_node) := by
    exact Iff.mp (normalization_5285 c0_node c1_node) (replay_2951 c0_node c1_node)
  have n1 : (shared_expr_Repair052_64 c0_node c1_node) := by
    exact Iff.mp (normalization_5289 c0_node c1_node) (replay_2952 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5290 c0_node c1_node) hn

end H4Formal.Generated.Repair
