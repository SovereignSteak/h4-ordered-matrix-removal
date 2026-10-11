import H4Formal.Certificates.CheckedRepair.Repair049

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_2818 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_1395 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact Iff.mp (replay_2817 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) i182

abbrev shared_expr_Repair050_0 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_1395 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_1395 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_1397 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_0 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_1145 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair050_1 (c1_group c1_mode c2_group c2_mode : Int) : Prop := (((((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c1_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair050_2 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := (((((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair050_1 c1_group c1_mode c2_group c2_mode)) ∨ ((¬ (((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair050_3 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair050_2 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c1_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair050_4 (c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode)))
abbrev shared_expr_Repair050_5 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair050_6 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair050_5 c1_node c1_sign c2_node c2_sign) ∨ ((¬ (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair050_7 (c1_node c2_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair050_8 (c1_node c1_sign c2_node : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_7 c1_node c2_node))
abbrev shared_expr_Repair050_9 (c1_node c2_node : Int) : Prop := ((¬ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair050_10 (c1_node c2_node c2_sign : Int) : Prop := ((((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair050_9 c1_node c2_node))
abbrev shared_expr_Repair050_11 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair050_10 c1_node c2_node c2_sign)))
abbrev shared_expr_Repair050_12 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair050_8 c1_node c1_sign c2_node)) ∨ (shared_expr_Repair050_11 c1_depth c1_node c2_depth c2_node c2_sign))
abbrev shared_expr_Repair050_13 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair050_6 c1_node c1_sign c2_node c2_sign)) ∨ ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair050_12 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
abbrev shared_expr_Repair050_14 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair050_13 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
abbrev shared_expr_Repair050_15 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair050_14 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
abbrev shared_expr_Repair050_16 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair050_15 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
abbrev shared_expr_Repair050_17 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair050_4 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair050_16 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair050_4 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair050_16 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_4920 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1397 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair050_17 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_4918 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_4918 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2819 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1397 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_1145 ((shared_expr_Repair050_4 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair050_16 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
  have hn := ht
  exact Iff.mpr (normalization_4920 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

-- Checked replay of mp.
theorem replay_2820 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_1395 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact Iff.mp (replay_2819 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2818 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182)

abbrev shared_expr_Repair050_18 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := (((c1_level = c2_level) ∧ (((c1_mode = c2_mode) ∧ (¬ ((c1_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ∨ ((¬ (c1_mode = c2_mode)) ∧ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) ∨ ((¬ (c1_level = c2_level)) ∧ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))
abbrev formula_1398 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := (shared_expr_Repair050_18 c1_group c1_level c1_mode c2_group c2_level c2_mode)

abbrev shared_expr_Repair050_19 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := ((((c1_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_1398 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c1_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c1_mode ≥ (4 : Int))))
abbrev formula_1399 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((¬ (c2_kind = (0 : Int))) ∨ (shared_expr_Repair050_19 c1_group c1_level c1_mode c2_group c2_level c2_mode))

abbrev shared_expr_Repair050_20 (c1_node c1_sign c2_node : Int) : Prop := ((((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ∧ (c1_sign = (0 : Int))) ∨ ((¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))))
abbrev formula_1400 (c1_node c1_sign c2_node : Int) : Prop := (shared_expr_Repair050_20 c1_node c1_sign c2_node)

abbrev shared_expr_Repair050_21 (c1_node c2_node c2_sign : Int) : Prop := ((((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ∧ (c2_sign = (1 : Int))) ∨ ((¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_1401 (c1_node c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_21 c1_node c2_node c2_sign)

abbrev shared_expr_Repair050_22 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ∧ (formula_1400 c1_node c1_sign c2_node)) ∨ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (-1 : Int))) ∧ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ∨ (formula_1401 c1_node c2_node c2_sign))))
abbrev formula_1402 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_22 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair050_23 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((c1_depth = c2_depth) ∧ (((c1_node = c2_node) ∧ ((c1_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c1_node = c2_node)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ∨ ((¬ (c1_depth = c2_depth)) ∧ (formula_1402 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
abbrev formula_1403 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_23 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair050_24 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (c2_kind = (0 : Int))) ∧ (((c1_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c1_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))))
abbrev formula_1404 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_24 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)

abbrev shared_expr_Repair050_25 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((c1_kind = (0 : Int)) ∧ (formula_1399 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) ∨ ((¬ (c1_kind = (0 : Int))) ∧ (formula_1404 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
abbrev formula_1405 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_25 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

abbrev shared_expr_Repair050_26 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_1395 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_1405 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_1406 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_26 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_1146 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ ((¬ p10) ∧ p11)) ∨ p12))))))))))) ↔ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ (p11 ∧ (¬ p10))) ∨ p12)))))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4921 (c1_group c2_group : Int) : ((c1_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)) ↔ (¬ ((c1_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4922 (c1_group c2_group : Int) : (¬ ((c1_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (¬ (¬ ((c1_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int)))) := (not_congr (normalization_4921 c1_group c2_group))

theorem normalization_4923 (c1_mode c2_mode : Int) : ((c1_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ↔ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4924 (c1_mode c2_mode : Int) : (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_4923 c1_mode c2_mode))

theorem normalization_4925 (c1_group c1_mode c2_group c2_mode : Int) : (((c1_mode = c2_mode) ∧ (¬ ((c1_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ∨ ((¬ (c1_mode = c2_mode)) ∧ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ↔ (shared_expr_Repair050_1 c1_group c1_mode c2_group c2_mode) := (or_congr (and_congr (normalization_4889 c1_mode c2_mode) (normalization_4922 c1_group c2_group)) (and_congr (not_congr (normalization_4889 c1_mode c2_mode)) (normalization_4924 c1_mode c2_mode)))

theorem normalization_4926 (c1_level c2_level : Int) : ((c1_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4927 (c1_level c2_level : Int) : (¬ ((c1_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4926 c1_level c2_level))

theorem normalization_4928 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : (formula_1398 c1_group c1_level c1_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair050_2 c1_group c1_level c1_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_4888 c1_level c2_level) (normalization_4925 c1_group c1_mode c2_group c2_mode)) (and_congr (not_congr (normalization_4888 c1_level c2_level)) (normalization_4927 c1_level c2_level)))

theorem normalization_4929 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : (shared_expr_Repair050_19 c1_group c1_level c1_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_4887 c1_mode c2_mode) (normalization_4928 c1_group c1_level c1_mode c2_group c2_level c2_mode)) (and_congr (not_congr (normalization_4887 c1_mode c2_mode)) (normalization_2160 c1_mode)))

theorem normalization_4930 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : (formula_1399 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode)) := (or_congr (normalization_2977 c2_kind) (normalization_4929 c1_group c1_level c1_mode c2_group c2_level c2_mode))

theorem normalization_4931 (c1_node c2_node : Int) : ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) ↔ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4932 (c1_node c2_node : Int) : (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4931 c1_node c2_node))

theorem normalization_4933 (c1_node c1_sign c2_node c2_sign : Int) : (((c1_node = c2_node) ∧ ((c1_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c1_node = c2_node)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (shared_expr_Repair050_6 c1_node c1_sign c2_node c2_sign) := (or_congr (and_congr (normalization_4868 c1_node c2_node) (normalization_4869 c1_sign c2_sign)) (and_congr (not_congr (normalization_4868 c1_node c2_node)) (normalization_4932 c1_node c2_node)))

theorem normalization_4934 (c1_depth c2_depth : Int) : ((c1_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_4935 (c1_node c2_node : Int) : ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_4936 (c1_node c2_node : Int) : ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4937 (c1_node c2_node : Int) : (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (not_congr (normalization_4936 c1_node c2_node))

theorem normalization_4938 (c1_node c1_sign c2_node : Int) : (formula_1400 c1_node c1_sign c2_node) ↔ (shared_expr_Repair050_8 c1_node c1_sign c2_node) := (or_congr (and_congr (normalization_4935 c1_node c2_node) (normalization_1449 c1_sign)) (and_congr (not_congr (normalization_4935 c1_node c2_node)) (normalization_4937 c1_node c2_node)))

theorem normalization_4939 (c1_depth c2_depth : Int) : ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := by
  omega

theorem normalization_4940 (c1_depth c2_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ (¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) := (not_congr (normalization_4939 c1_depth c2_depth))

theorem normalization_4941 (c1_node c2_node : Int) : ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_4942 (c1_node c2_node : Int) : ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4943 (c1_node c2_node : Int) : (¬ ((c2_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4942 c1_node c2_node))

theorem normalization_4944 (c1_node c2_node c2_sign : Int) : (formula_1401 c1_node c2_node c2_sign) ↔ (shared_expr_Repair050_10 c1_node c2_node c2_sign) := (or_congr (and_congr (normalization_4941 c1_node c2_node) (normalization_26 c2_sign)) (and_congr (not_congr (normalization_4941 c1_node c2_node)) (normalization_4943 c1_node c2_node)))

theorem normalization_4945 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ∨ (formula_1401 c1_node c2_node c2_sign)) ↔ ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair050_10 c1_node c2_node c2_sign)) := (or_congr (normalization_4940 c1_depth c2_depth) (normalization_4944 c1_node c2_node c2_sign))

abbrev shared_expr_Repair050_27 (c1_depth c1_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair050_10 c1_node c2_node c2_sign)))
abbrev shared_expr_Repair050_28 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair050_8 c1_node c1_sign c2_node)) ∨ (shared_expr_Repair050_27 c1_depth c1_node c2_depth c2_node c2_sign))
theorem normalization_4946 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : (formula_1402 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair050_28 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_4934 c1_depth c2_depth) (normalization_4938 c1_node c1_sign c2_node)) (and_congr (not_congr (normalization_4934 c1_depth c2_depth)) (normalization_4945 c1_depth c1_node c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair050_29 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair050_6 c1_node c1_sign c2_node c2_sign)) ∨ ((¬ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair050_28 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
theorem normalization_4947 (c1_depth c1_node c1_sign c2_depth c2_node c2_sign : Int) : (formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair050_29 c1_depth c1_node c1_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_4867 c1_depth c2_depth) (normalization_4933 c1_node c1_sign c2_node c2_sign)) (and_congr (not_congr (normalization_4867 c1_depth c2_depth)) (normalization_4946 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))

theorem normalization_4948 (c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : ((¬ (c2_kind = (2 : Int))) ∧ (formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) ↔ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair050_29 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)) := (and_congr (normalization_2991 c2_kind) (normalization_4947 c1_depth c1_node c1_sign c2_depth c2_node c2_sign))

abbrev shared_expr_Repair050_30 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair050_29 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))
abbrev shared_expr_Repair050_31 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair050_30 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))
theorem normalization_4949 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (((c1_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c1_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_1403 c1_depth c1_node c1_sign c2_depth c2_node c2_sign)))) ↔ (shared_expr_Repair050_31 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_1446 c1_kind) (normalization_16 c2_kind)) (and_congr (not_congr (normalization_1446 c1_kind)) (normalization_4948 c1_depth c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))

theorem normalization_4950 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1404 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign) ↔ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair050_31 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := (and_congr (normalization_2977 c2_kind) (normalization_4949 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair050_32 (c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair050_31 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_4951 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1405 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ ((shared_expr_Repair050_4 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair050_32 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) := (or_congr (and_congr (normalization_1439 c1_kind) (normalization_4930 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) (and_congr (not_congr (normalization_1439 c1_kind)) (normalization_4950 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair050_33 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair050_4 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair050_16 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair050_4 c1_group c1_kind c1_level c1_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair050_32 c1_depth c1_kind c1_node c1_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_4952 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1406 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair050_33 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_4918 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_4951 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2821 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_1406 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_1146 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode)) (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (shared_expr_Repair050_6 c1_node c1_sign c2_node c2_sign) (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) (shared_expr_Repair050_8 c1_node c1_sign c2_node) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) (shared_expr_Repair050_10 c1_node c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_4952 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

-- Checked replay of mp.
theorem replay_2822 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_1405 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact Iff.mp (replay_2821 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2820 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i182)

abbrev shared_expr_Repair050_34 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := ((shared_expr_Repair050_19 c1_group c1_level c1_mode c2_group c2_level c2_mode) ↔ ((((c1_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_342 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c1_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c1_mode ≥ (4 : Int)))))
abbrev formula_1407 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := (shared_expr_Repair050_34 c1_group c1_level c1_mode c2_group c2_level c2_mode)

theorem normalized_1147 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4953 (c1_level c2_level : Int) : ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4954 (c1_level c2_level : Int) : (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := (not_congr (normalization_4953 c1_level c2_level))

theorem normalization_4955 (c1_level c2_level : Int) : ((¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ ((¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) := (or_congr (normalization_4954 c1_level c2_level) (normalization_4927 c1_level c2_level))

theorem normalization_4956 (c1_mode c2_mode : Int) : ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ↔ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_4957 (c1_mode c2_mode : Int) : (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) := (not_congr (normalization_4956 c1_mode c2_mode))

theorem normalization_4958 (c1_mode c2_mode : Int) : ((¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_4957 c1_mode c2_mode) (normalization_4924 c1_mode c2_mode))

abbrev shared_expr_Repair050_35 (c1_group c1_mode c2_group c2_mode : Int) : Prop := ((((¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c1_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))))
theorem normalization_4959 (c1_group c1_mode c2_group c2_mode : Int) : (formula_340 c1_group c1_mode c2_group c2_mode) ↔ (shared_expr_Repair050_35 c1_group c1_mode c2_group c2_mode) := (or_congr (and_congr (normalization_4958 c1_mode c2_mode) (normalization_4924 c1_mode c2_mode)) (and_congr (not_congr (normalization_4958 c1_mode c2_mode)) (normalization_4922 c1_group c2_group)))

abbrev shared_expr_Repair050_36 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair050_35 c1_group c1_mode c2_group c2_mode)))
theorem normalization_4960 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : (formula_342 c1_group c1_level c1_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair050_36 c1_group c1_level c1_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_4955 c1_level c2_level) (normalization_4927 c1_level c2_level)) (and_congr (not_congr (normalization_4955 c1_level c2_level)) (normalization_4959 c1_group c1_mode c2_group c2_mode)))

abbrev shared_expr_Repair050_37 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair050_36 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c1_mode) ≤ (3 : Int)))))
theorem normalization_4961 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : ((((c1_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_342 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c1_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c1_mode ≥ (4 : Int)))) ↔ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_4887 c1_mode c2_mode) (normalization_4960 c1_group c1_level c1_mode c2_group c2_level c2_mode)) (and_congr (not_congr (normalization_4887 c1_mode c2_mode)) (normalization_2160 c1_mode)))

theorem normalization_4962 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : (formula_1407 c1_group c1_level c1_mode c2_group c2_level c2_mode) ↔ ((shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)) := (iff_congr (normalization_4929 c1_group c1_level c1_mode c2_group c2_level c2_mode) (normalization_4961 c1_group c1_level c1_mode c2_group c2_level c2_mode))

-- Checked replay of rewrite.
theorem replay_2823 (c1_group c1_level c1_mode c2_group c2_level c2_mode : Int) : (formula_1407 c1_group c1_level c1_mode c2_group c2_level c2_mode) := by
  classical
  have ht := (normalized_1147 ((¬ ((c1_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ((c1_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((c1_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ((c1_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)) ((c1_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int)) ((c1_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4962 c1_group c1_level c1_mode c2_group c2_level c2_mode) hn

abbrev shared_expr_Repair050_38 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∨ ((((c1_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_342 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c1_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c1_mode ≥ (4 : Int)))))
abbrev formula_1408 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (shared_expr_Repair050_38 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)

theorem normalized_1148 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4963 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : (formula_1408 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)) := (or_congr (normalization_1002 c2_kind) (normalization_4961 c1_group c1_level c1_mode c2_group c2_level c2_mode))

abbrev shared_expr_Repair050_39 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)))
theorem normalization_4964 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_1399 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_1408 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Repair050_39 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_4930 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) (normalization_4963 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of monotonicity.
theorem replay_2824 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_1399 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_1408 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_1148 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode) (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode))
  have n0 : ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_3048 c2_kind) (replay_2144 c2_kind)
  have n1 : ((shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)) := by
    exact Iff.mp (normalization_4962 c1_group c1_level c1_mode c2_group c2_level c2_mode) (replay_2823 c1_group c1_level c1_mode c2_group c2_level c2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4964 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_1149 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4965 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : (formula_1382 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)) := (or_congr (normalization_79 c2_kind) (or_congr (normalization_81 c2_kind) (normalization_4961 c1_group c1_level c1_mode c2_group c2_level c2_mode)))

abbrev shared_expr_Repair050_40 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)))
theorem normalization_4966 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_1408 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_1382 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Repair050_40 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_4963 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) (normalization_4965 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of rewrite.
theorem replay_2825 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_1408 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_1382 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_1149 ((c2_kind) ≤ (0 : Int)) ((c2_kind) ≤ (-1 : Int)) (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode))
  have hn := ht
  exact Iff.mpr (normalization_4966 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_1150 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair050_41 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)))
theorem normalization_4967 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_1399 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_1382 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Repair050_41 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_4930 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) (normalization_4965 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of trans.
theorem replay_2826 (c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_1399 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_1382 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_1150 ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_3 c1_group c1_level c1_mode c2_group c2_level c2_mode)) (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair050_37 c1_group c1_level c1_mode c2_group c2_level c2_mode)))
  have n0 : (shared_expr_Repair050_39 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) := by
    exact Iff.mp (normalization_4964 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) (replay_2824 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)
  have n1 : (shared_expr_Repair050_40 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) := by
    exact Iff.mp (normalization_4966 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) (replay_2825 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4967 c1_group c1_level c1_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_1151 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4968 (c1_depth c2_depth : Int) : (c1_depth ≤ c2_depth) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4969 (c1_depth c2_depth : Int) : (c1_depth ≥ c2_depth) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4970 (c1_depth c2_depth : Int) : ((c1_depth ≤ c2_depth) ∧ (c1_depth ≥ c2_depth)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_4968 c1_depth c2_depth) (normalization_4969 c1_depth c2_depth))

abbrev shared_expr_Repair050_42 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
theorem normalization_4971 (c1_depth c2_depth : Int) : ((c1_depth = c2_depth) ↔ ((c1_depth ≤ c2_depth) ∧ (c1_depth ≥ c2_depth))) ↔ (shared_expr_Repair050_42 c1_depth c2_depth) := (iff_congr (normalization_4867 c1_depth c2_depth) (normalization_4970 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2827 (c1_depth c2_depth : Int) : ((c1_depth = c2_depth) ↔ ((c1_depth ≤ c2_depth) ∧ (c1_depth ≥ c2_depth))) := by
  classical
  have ht := (normalized_1151 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4971 c1_depth c2_depth) hn

theorem normalized_1152 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4972 (c1_depth c2_depth : Int) : ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4973 (c1_depth c2_depth : Int) : ((c1_depth ≤ c2_depth) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := (iff_congr (normalization_4968 c1_depth c2_depth) (normalization_4972 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2828 (c1_depth c2_depth : Int) : ((c1_depth ≤ c2_depth) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1152 ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4973 c1_depth c2_depth) hn

theorem normalized_1153 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4974 (c1_depth c2_depth : Int) : ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4975 (c1_depth c2_depth : Int) : ((c1_depth ≥ c2_depth) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_4969 c1_depth c2_depth) (normalization_4974 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2829 (c1_depth c2_depth : Int) : ((c1_depth ≥ c2_depth) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1153 ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4975 c1_depth c2_depth) hn

theorem normalized_1154 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4976 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_4972 c1_depth c2_depth) (normalization_4974 c1_depth c2_depth))

theorem normalization_4977 (c1_depth c2_depth : Int) : (((c1_depth ≤ c2_depth) ∧ (c1_depth ≥ c2_depth)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Repair050_42 c1_depth c2_depth) := (iff_congr (normalization_4970 c1_depth c2_depth) (normalization_4976 c1_depth c2_depth))

-- Checked replay of monotonicity.
theorem replay_2830 (c1_depth c2_depth : Int) : (((c1_depth ≤ c2_depth) ∧ (c1_depth ≥ c2_depth)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1154 ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
  have n0 : (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4973 c1_depth c2_depth) (replay_2828 c1_depth c2_depth)
  have n1 : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4975 c1_depth c2_depth) (replay_2829 c1_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4977 c1_depth c2_depth) hn

abbrev shared_expr_Repair050_43 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))))
abbrev formula_1409 (c1_depth c2_depth : Int) : Prop := (shared_expr_Repair050_43 c1_depth c2_depth)

theorem normalized_1155 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4978 (c1_depth c2_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := (not_congr (normalization_4972 c1_depth c2_depth))

theorem normalization_4979 (c1_depth c2_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_4974 c1_depth c2_depth))

theorem normalization_4980 (c1_depth c2_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_4978 c1_depth c2_depth) (normalization_4979 c1_depth c2_depth))

theorem normalization_4981 (c1_depth c2_depth : Int) : (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_4980 c1_depth c2_depth))

abbrev shared_expr_Repair050_44 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))))
theorem normalization_4982 (c1_depth c2_depth : Int) : (formula_1409 c1_depth c2_depth) ↔ (shared_expr_Repair050_44 c1_depth c2_depth) := (iff_congr (normalization_4976 c1_depth c2_depth) (normalization_4981 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2831 (c1_depth c2_depth : Int) : (formula_1409 c1_depth c2_depth) := by
  classical
  have ht := (normalized_1155 ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4982 c1_depth c2_depth) hn

theorem normalized_1156 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4983 (c1_depth c2_depth : Int) : (((c1_depth ≤ c2_depth) ∧ (c1_depth ≥ c2_depth)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair050_44 c1_depth c2_depth) := (iff_congr (normalization_4970 c1_depth c2_depth) (normalization_4981 c1_depth c2_depth))

-- Checked replay of trans.
theorem replay_2832 (c1_depth c2_depth : Int) : (((c1_depth ≤ c2_depth) ∧ (c1_depth ≥ c2_depth)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1156 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (shared_expr_Repair050_44 c1_depth c2_depth))
  have n0 : (shared_expr_Repair050_42 c1_depth c2_depth) := by
    exact Iff.mp (normalization_4977 c1_depth c2_depth) (replay_2830 c1_depth c2_depth)
  have n1 : (shared_expr_Repair050_44 c1_depth c2_depth) := by
    exact Iff.mp (normalization_4982 c1_depth c2_depth) (replay_2831 c1_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4983 c1_depth c2_depth) hn

theorem normalized_1157 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4984 (c1_depth c2_depth : Int) : ((c1_depth = c2_depth) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair050_44 c1_depth c2_depth) := (iff_congr (normalization_4867 c1_depth c2_depth) (normalization_4981 c1_depth c2_depth))

-- Checked replay of trans.
theorem replay_2833 (c1_depth c2_depth : Int) : ((c1_depth = c2_depth) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1157 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (shared_expr_Repair050_44 c1_depth c2_depth))
  have n0 : (shared_expr_Repair050_42 c1_depth c2_depth) := by
    exact Iff.mp (normalization_4971 c1_depth c2_depth) (replay_2827 c1_depth c2_depth)
  have n1 : (shared_expr_Repair050_44 c1_depth c2_depth) := by
    exact Iff.mp (normalization_4983 c1_depth c2_depth) (replay_2832 c1_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4984 c1_depth c2_depth) hn

theorem normalized_1158 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4985 (c1_node c2_node : Int) : (c1_node ≤ c2_node) ↔ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4986 (c1_node c2_node : Int) : (c1_node ≥ c2_node) ↔ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4987 (c1_node c2_node : Int) : ((c1_node ≤ c2_node) ∧ (c1_node ≥ c2_node)) ↔ (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_4985 c1_node c2_node) (normalization_4986 c1_node c2_node))

abbrev shared_expr_Repair050_45 (c1_node c2_node : Int) : Prop := ((((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ↔ (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_4988 (c1_node c2_node : Int) : ((c1_node = c2_node) ↔ ((c1_node ≤ c2_node) ∧ (c1_node ≥ c2_node))) ↔ (shared_expr_Repair050_45 c1_node c2_node) := (iff_congr (normalization_4868 c1_node c2_node) (normalization_4987 c1_node c2_node))

-- Checked replay of rewrite.
theorem replay_2834 (c1_node c2_node : Int) : ((c1_node = c2_node) ↔ ((c1_node ≤ c2_node) ∧ (c1_node ≥ c2_node))) := by
  classical
  have ht := (normalized_1158 (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4988 c1_node c2_node) hn

theorem normalized_1159 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4989 (c1_node c2_node : Int) : ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4990 (c1_node c2_node : Int) : ((c1_node ≤ c2_node) ↔ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (iff_congr (normalization_4985 c1_node c2_node) (normalization_4989 c1_node c2_node))

-- Checked replay of rewrite.
theorem replay_2835 (c1_node c2_node : Int) : ((c1_node ≤ c2_node) ↔ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1159 ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4990 c1_node c2_node) hn

theorem normalized_1160 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4991 (c1_node c2_node : Int) : ((c1_node ≥ c2_node) ↔ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_4986 c1_node c2_node) (normalization_4931 c1_node c2_node))

-- Checked replay of rewrite.
theorem replay_2836 (c1_node c2_node : Int) : ((c1_node ≥ c2_node) ↔ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1160 ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4991 c1_node c2_node) hn

theorem normalized_1161 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4992 (c1_node c2_node : Int) : (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_4989 c1_node c2_node) (normalization_4931 c1_node c2_node))

theorem normalization_4993 (c1_node c2_node : Int) : (((c1_node ≤ c2_node) ∧ (c1_node ≥ c2_node)) ↔ (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair050_45 c1_node c2_node) := (iff_congr (normalization_4987 c1_node c2_node) (normalization_4992 c1_node c2_node))

-- Checked replay of monotonicity.
theorem replay_2837 (c1_node c2_node : Int) : (((c1_node ≤ c2_node) ∧ (c1_node ≥ c2_node)) ↔ (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1161 ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
  have n0 : (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_4990 c1_node c2_node) (replay_2835 c1_node c2_node)
  have n1 : ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_4991 c1_node c2_node) (replay_2836 c1_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4993 c1_node c2_node) hn

abbrev shared_expr_Repair050_46 (c1_node c2_node : Int) : Prop := ((((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))))
abbrev formula_1410 (c1_node c2_node : Int) : Prop := (shared_expr_Repair050_46 c1_node c2_node)

theorem normalized_1162 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4994 (c1_node c2_node : Int) : (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_4989 c1_node c2_node))

theorem normalization_4995 (c1_node c2_node : Int) : ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) := (or_congr (normalization_4994 c1_node c2_node) (normalization_4932 c1_node c2_node))

theorem normalization_4996 (c1_node c2_node : Int) : (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_4995 c1_node c2_node))

abbrev shared_expr_Repair050_47 (c1_node c2_node : Int) : Prop := ((((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))))
theorem normalization_4997 (c1_node c2_node : Int) : (formula_1410 c1_node c2_node) ↔ (shared_expr_Repair050_47 c1_node c2_node) := (iff_congr (normalization_4992 c1_node c2_node) (normalization_4996 c1_node c2_node))

-- Checked replay of rewrite.
theorem replay_2838 (c1_node c2_node : Int) : (formula_1410 c1_node c2_node) := by
  classical
  have ht := (normalized_1162 ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4997 c1_node c2_node) hn

theorem normalized_1163 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4998 (c1_node c2_node : Int) : (((c1_node ≤ c2_node) ∧ (c1_node ≥ c2_node)) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair050_47 c1_node c2_node) := (iff_congr (normalization_4987 c1_node c2_node) (normalization_4996 c1_node c2_node))

-- Checked replay of trans.
theorem replay_2839 (c1_node c2_node : Int) : (((c1_node ≤ c2_node) ∧ (c1_node ≥ c2_node)) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1163 (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) (shared_expr_Repair050_47 c1_node c2_node))
  have n0 : (shared_expr_Repair050_45 c1_node c2_node) := by
    exact Iff.mp (normalization_4993 c1_node c2_node) (replay_2837 c1_node c2_node)
  have n1 : (shared_expr_Repair050_47 c1_node c2_node) := by
    exact Iff.mp (normalization_4997 c1_node c2_node) (replay_2838 c1_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4998 c1_node c2_node) hn

theorem normalized_1164 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4999 (c1_node c2_node : Int) : ((c1_node = c2_node) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair050_47 c1_node c2_node) := (iff_congr (normalization_4868 c1_node c2_node) (normalization_4996 c1_node c2_node))

-- Checked replay of trans.
theorem replay_2840 (c1_node c2_node : Int) : ((c1_node = c2_node) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1164 (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) (shared_expr_Repair050_47 c1_node c2_node))
  have n0 : (shared_expr_Repair050_45 c1_node c2_node) := by
    exact Iff.mp (normalization_4988 c1_node c2_node) (replay_2834 c1_node c2_node)
  have n1 : (shared_expr_Repair050_47 c1_node c2_node) := by
    exact Iff.mp (normalization_4998 c1_node c2_node) (replay_2839 c1_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4999 c1_node c2_node) hn

theorem normalized_1165 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5000 (c1_sign : Int) : ((c1_sign ≤ (0 : Int)) ∧ (c1_sign ≥ (0 : Int))) ↔ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) := (and_congr (normalization_1797 c1_sign) (normalization_1799 c1_sign))

theorem normalization_5001 (c1_sign : Int) : ((c1_sign = (0 : Int)) ↔ ((c1_sign ≤ (0 : Int)) ∧ (c1_sign ≥ (0 : Int)))) ↔ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int))))) := (iff_congr (normalization_1449 c1_sign) (normalization_5000 c1_sign))

-- Checked replay of rewrite.
theorem replay_2841 (c1_sign : Int) : ((c1_sign = (0 : Int)) ↔ ((c1_sign ≤ (0 : Int)) ∧ (c1_sign ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1165 (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5001 c1_sign) hn

theorem normalized_1166 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5002 (c1_sign : Int) : (((c1_sign ≤ (0 : Int)) ∧ (c1_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int)))))) ↔ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_5000 c1_sign) (normalization_1802 c1_sign))

-- Checked replay of rewrite.
theorem replay_2842 (c1_sign : Int) : (((c1_sign ≤ (0 : Int)) ∧ (c1_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1166 ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5002 c1_sign) hn

theorem normalized_1167 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5003 (c1_sign : Int) : ((c1_sign = (0 : Int)) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int)))))) ↔ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_1449 c1_sign) (normalization_1802 c1_sign))

-- Checked replay of trans.
theorem replay_2843 (c1_sign : Int) : ((c1_sign = (0 : Int)) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1167 (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))))
  have n0 : ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_5001 c1_sign) (replay_2841 c1_sign)
  have n1 : ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_5002 c1_sign) (replay_2842 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5003 c1_sign) hn

theorem normalized_1168 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5004 (c1_sign c2_sign : Int) : ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := (and_congr (normalization_1802 c1_sign) (normalization_119 c2_sign))

abbrev shared_expr_Repair050_48 (c1_sign c2_sign : Int) : Prop := (((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))))
theorem normalization_5005 (c1_sign c2_sign : Int) : (((c1_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) ↔ (shared_expr_Repair050_48 c1_sign c2_sign) := (iff_congr (normalization_4869 c1_sign c2_sign) (normalization_5004 c1_sign c2_sign))

-- Checked replay of monotonicity.
theorem replay_2844 (c1_sign c2_sign : Int) : (((c1_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_1168 (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))) (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))
  have n0 : ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_5003 c1_sign) (replay_2843 c1_sign)
  have n1 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3121 c2_sign) (replay_2180 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5005 c1_sign c2_sign) hn

abbrev shared_expr_Repair050_49 (c1_sign c2_sign : Int) : Prop := (((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev formula_1411 (c1_sign c2_sign : Int) : Prop := (shared_expr_Repair050_49 c1_sign c2_sign)

theorem normalized_1169 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5006 (c1_sign c2_sign : Int) : ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) ↔ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) := (or_congr (normalization_1798 c1_sign) (or_congr (normalization_1800 c1_sign) (or_congr (normalization_115 c2_sign) (normalization_117 c2_sign))))

theorem normalization_5007 (c1_sign c2_sign : Int) : (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) := (not_congr (normalization_5006 c1_sign c2_sign))

abbrev shared_expr_Repair050_50 (c1_sign c2_sign : Int) : Prop := (((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
theorem normalization_5008 (c1_sign c2_sign : Int) : (formula_1411 c1_sign c2_sign) ↔ (shared_expr_Repair050_50 c1_sign c2_sign) := (iff_congr (normalization_5004 c1_sign c2_sign) (normalization_5007 c1_sign c2_sign))

-- Checked replay of rewrite.
theorem replay_2845 (c1_sign c2_sign : Int) : (formula_1411 c1_sign c2_sign) := by
  classical
  have ht := (normalized_1169 ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)) ((c2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5008 c1_sign c2_sign) hn

theorem normalized_1170 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair050_51 (c1_sign c2_sign : Int) : Prop := (((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
theorem normalization_5009 (c1_sign c2_sign : Int) : (((c1_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ (shared_expr_Repair050_51 c1_sign c2_sign) := (iff_congr (normalization_4869 c1_sign c2_sign) (normalization_5007 c1_sign c2_sign))

-- Checked replay of trans.
theorem replay_2846 (c1_sign c2_sign : Int) : (((c1_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1170 ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair050_48 c1_sign c2_sign) := by
    exact Iff.mp (normalization_5005 c1_sign c2_sign) (replay_2844 c1_sign c2_sign)
  have n1 : (shared_expr_Repair050_50 c1_sign c2_sign) := by
    exact Iff.mp (normalization_5008 c1_sign c2_sign) (replay_2845 c1_sign c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5009 c1_sign c2_sign) hn

abbrev shared_expr_Repair050_52 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair050_53 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair050_52 c1_node c1_sign c2_node c2_sign) ∨ ((¬ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))
abbrev formula_1412 (c1_node c1_sign c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_53 c1_node c1_sign c2_node c2_sign)

abbrev shared_expr_Repair050_54 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((((c1_node = c2_node) ∧ ((c1_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c1_node = c2_node)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (formula_1412 c1_node c1_sign c2_node c2_sign))
abbrev formula_1413 (c1_node c1_sign c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_54 c1_node c1_sign c2_node c2_sign)

theorem normalized_1171 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair050_55 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair050_56 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair050_55 c1_node c1_sign c2_node c2_sign) ∨ ((¬ (¬ ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
theorem normalization_5010 (c1_node c1_sign c2_node c2_sign : Int) : (formula_1412 c1_node c1_sign c2_node c2_sign) ↔ (shared_expr_Repair050_56 c1_node c1_sign c2_node c2_sign) := (or_congr (and_congr (normalization_4996 c1_node c2_node) (normalization_5007 c1_sign c2_sign)) (and_congr (not_congr (normalization_4996 c1_node c2_node)) (normalization_4932 c1_node c2_node)))

theorem normalization_5011 (c1_node c1_sign c2_node c2_sign : Int) : (formula_1413 c1_node c1_sign c2_node c2_sign) ↔ ((shared_expr_Repair050_6 c1_node c1_sign c2_node c2_sign) ↔ (shared_expr_Repair050_56 c1_node c1_sign c2_node c2_sign)) := (iff_congr (normalization_4933 c1_node c1_sign c2_node c2_sign) (normalization_5010 c1_node c1_sign c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2847 (c1_node c1_sign c2_node c2_sign : Int) : (formula_1413 c1_node c1_sign c2_node c2_sign) := by
  classical
  have ht := (normalized_1171 (((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair050_47 c1_node c2_node) := by
    exact Iff.mp (normalization_4999 c1_node c2_node) (replay_2840 c1_node c2_node)
  have n1 : (shared_expr_Repair050_51 c1_sign c2_sign) := by
    exact Iff.mp (normalization_5009 c1_sign c2_sign) (replay_2846 c1_sign c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5011 c1_node c1_sign c2_node c2_sign) hn

theorem normalized_1172 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair050_57 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair050_55 c1_node c1_sign c2_node c2_sign))
theorem normalization_5012 (c1_node c1_sign c2_node c2_sign : Int) : (formula_1379 c1_node c1_sign c2_node c2_sign) ↔ (shared_expr_Repair050_57 c1_node c1_sign c2_node c2_sign) := (or_congr (and_congr (normalization_4995 c1_node c2_node) (normalization_4932 c1_node c2_node)) (and_congr (not_congr (normalization_4995 c1_node c2_node)) (normalization_5007 c1_sign c2_sign)))

theorem normalization_5013 (c1_node c1_sign c2_node c2_sign : Int) : ((formula_1412 c1_node c1_sign c2_node c2_sign) ↔ (formula_1379 c1_node c1_sign c2_node c2_sign)) ↔ ((shared_expr_Repair050_56 c1_node c1_sign c2_node c2_sign) ↔ (shared_expr_Repair050_57 c1_node c1_sign c2_node c2_sign)) := (iff_congr (normalization_5010 c1_node c1_sign c2_node c2_sign) (normalization_5012 c1_node c1_sign c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2848 (c1_node c1_sign c2_node c2_sign : Int) : ((formula_1412 c1_node c1_sign c2_node c2_sign) ↔ (formula_1379 c1_node c1_sign c2_node c2_sign)) := by
  classical
  have ht := (normalized_1172 ((¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) ((c1_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5013 c1_node c1_sign c2_node c2_sign) hn

abbrev shared_expr_Repair050_58 (c1_node c1_sign c2_node c2_sign : Int) : Prop := ((((c1_node = c2_node) ∧ ((c1_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c1_node = c2_node)) ∧ (¬ ((c1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (formula_1379 c1_node c1_sign c2_node c2_sign))
abbrev formula_1414 (c1_node c1_sign c2_node c2_sign : Int) : Prop := (shared_expr_Repair050_58 c1_node c1_sign c2_node c2_sign)

theorem normalized_1173 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5014 (c1_node c1_sign c2_node c2_sign : Int) : (formula_1414 c1_node c1_sign c2_node c2_sign) ↔ ((shared_expr_Repair050_6 c1_node c1_sign c2_node c2_sign) ↔ (shared_expr_Repair050_57 c1_node c1_sign c2_node c2_sign)) := (iff_congr (normalization_4933 c1_node c1_sign c2_node c2_sign) (normalization_5012 c1_node c1_sign c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2849 (c1_node c1_sign c2_node c2_sign : Int) : (formula_1414 c1_node c1_sign c2_node c2_sign) := by
  classical
  have ht := (normalized_1173 (shared_expr_Repair050_6 c1_node c1_sign c2_node c2_sign) (shared_expr_Repair050_56 c1_node c1_sign c2_node c2_sign) (shared_expr_Repair050_57 c1_node c1_sign c2_node c2_sign))
  have n0 : ((shared_expr_Repair050_6 c1_node c1_sign c2_node c2_sign) ↔ (shared_expr_Repair050_56 c1_node c1_sign c2_node c2_sign)) := by
    exact Iff.mp (normalization_5011 c1_node c1_sign c2_node c2_sign) (replay_2847 c1_node c1_sign c2_node c2_sign)
  have n1 : ((shared_expr_Repair050_56 c1_node c1_sign c2_node c2_sign) ↔ (shared_expr_Repair050_57 c1_node c1_sign c2_node c2_sign)) := by
    exact Iff.mp (normalization_5013 c1_node c1_sign c2_node c2_sign) (replay_2848 c1_node c1_sign c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5014 c1_node c1_sign c2_node c2_sign) hn

theorem normalized_1174 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5015 (c1_depth c2_depth : Int) : ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5016 (c1_depth c2_depth : Int) : ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_5017 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_5015 c1_depth c2_depth) (normalization_5016 c1_depth c2_depth))

abbrev shared_expr_Repair050_59 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))
theorem normalization_5018 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Repair050_59 c1_depth c2_depth) := (iff_congr (normalization_4934 c1_depth c2_depth) (normalization_5017 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2850 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_1174 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5018 c1_depth c2_depth) hn

abbrev shared_expr_Repair050_60 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))))
abbrev formula_1415 (c1_depth c2_depth : Int) : Prop := (shared_expr_Repair050_60 c1_depth c2_depth)

theorem normalized_1175 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5019 (c1_depth c2_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := (not_congr (normalization_5015 c1_depth c2_depth))

theorem normalization_5020 (c1_depth c2_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_5016 c1_depth c2_depth))

theorem normalization_5021 (c1_depth c2_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_5019 c1_depth c2_depth) (normalization_5020 c1_depth c2_depth))

theorem normalization_5022 (c1_depth c2_depth : Int) : (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_5021 c1_depth c2_depth))

abbrev shared_expr_Repair050_61 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))))
theorem normalization_5023 (c1_depth c2_depth : Int) : (formula_1415 c1_depth c2_depth) ↔ (shared_expr_Repair050_61 c1_depth c2_depth) := (iff_congr (normalization_5017 c1_depth c2_depth) (normalization_5022 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2851 (c1_depth c2_depth : Int) : (formula_1415 c1_depth c2_depth) := by
  classical
  have ht := (normalized_1175 ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5023 c1_depth c2_depth) hn

theorem normalized_1176 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5024 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Repair050_61 c1_depth c2_depth) := (iff_congr (normalization_4934 c1_depth c2_depth) (normalization_5022 c1_depth c2_depth))

-- Checked replay of trans.
theorem replay_2852 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_1176 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) (shared_expr_Repair050_61 c1_depth c2_depth))
  have n0 : (shared_expr_Repair050_59 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5018 c1_depth c2_depth) (replay_2850 c1_depth c2_depth)
  have n1 : (shared_expr_Repair050_61 c1_depth c2_depth) := by
    exact Iff.mp (normalization_5023 c1_depth c2_depth) (replay_2851 c1_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5024 c1_depth c2_depth) hn

theorem normalized_1177 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5025 (c1_node c2_node : Int) : ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5026 (c1_node c2_node : Int) : (((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (and_congr (normalization_5025 c1_node c2_node) (normalization_4936 c1_node c2_node))

abbrev shared_expr_Repair050_62 (c1_node c2_node : Int) : Prop := (((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_5027 (c1_node c2_node : Int) : (((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Repair050_62 c1_node c2_node) := (iff_congr (normalization_4935 c1_node c2_node) (normalization_5026 c1_node c2_node))

-- Checked replay of rewrite.
theorem replay_2853 (c1_node c2_node : Int) : (((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1177 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5027 c1_node c2_node) hn

abbrev shared_expr_Repair050_63 (c1_node c2_node : Int) : Prop := ((((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1416 (c1_node c2_node : Int) : Prop := (shared_expr_Repair050_63 c1_node c2_node)

theorem normalized_1178 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5028 (c1_node c2_node : Int) : (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5025 c1_node c2_node))

theorem normalization_5029 (c1_node c2_node : Int) : ((¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) := (or_congr (normalization_5028 c1_node c2_node) (normalization_4937 c1_node c2_node))

theorem normalization_5030 (c1_node c2_node : Int) : (¬ ((¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) := (not_congr (normalization_5029 c1_node c2_node))

abbrev shared_expr_Repair050_64 (c1_node c2_node : Int) : Prop := (((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))))
theorem normalization_5031 (c1_node c2_node : Int) : (formula_1416 c1_node c2_node) ↔ (shared_expr_Repair050_64 c1_node c2_node) := (iff_congr (normalization_5026 c1_node c2_node) (normalization_5030 c1_node c2_node))

-- Checked replay of rewrite.
theorem replay_2854 (c1_node c2_node : Int) : (formula_1416 c1_node c2_node) := by
  classical
  have ht := (normalized_1178 (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5031 c1_node c2_node) hn

abbrev shared_expr_Repair050_65 (c1_node c2_node : Int) : Prop := (((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1417 (c1_node c2_node : Int) : Prop := (shared_expr_Repair050_65 c1_node c2_node)

theorem normalized_1179 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5032 (c1_node c2_node : Int) : (formula_1417 c1_node c2_node) ↔ (shared_expr_Repair050_64 c1_node c2_node) := (iff_congr (normalization_4935 c1_node c2_node) (normalization_5030 c1_node c2_node))

-- Checked replay of trans.
theorem replay_2855 (c1_node c2_node : Int) : (formula_1417 c1_node c2_node) := by
  classical
  have ht := (normalized_1179 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) (shared_expr_Repair050_64 c1_node c2_node))
  have n0 : (shared_expr_Repair050_62 c1_node c2_node) := by
    exact Iff.mp (normalization_5027 c1_node c2_node) (replay_2853 c1_node c2_node)
  have n1 : (shared_expr_Repair050_64 c1_node c2_node) := by
    exact Iff.mp (normalization_5031 c1_node c2_node) (replay_2854 c1_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5032 c1_node c2_node) hn

abbrev shared_expr_Repair050_66 (c1_node c1_sign c2_node : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))))
abbrev shared_expr_Repair050_67 (c1_node c2_node : Int) : Prop := ((¬ (¬ ((¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_1418 (c1_node c1_sign c2_node : Int) : Prop := ((shared_expr_Repair050_66 c1_node c1_sign c2_node) ∨ (shared_expr_Repair050_67 c1_node c2_node))

theorem normalized_1180 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair050_68 (c1_node c1_sign c2_node : Int) : Prop := ((¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Repair050_69 (c1_node c2_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_5033 (c1_node c1_sign c2_node : Int) : (formula_1418 c1_node c1_sign c2_node) ↔ ((shared_expr_Repair050_68 c1_node c1_sign c2_node) ∨ (shared_expr_Repair050_69 c1_node c2_node)) := (or_congr (and_congr (normalization_5030 c1_node c2_node) (normalization_1802 c1_sign)) (and_congr (not_congr (normalization_5030 c1_node c2_node)) (normalization_4937 c1_node c2_node)))

theorem normalization_5034 (c1_node c1_sign c2_node : Int) : ((formula_1400 c1_node c1_sign c2_node) ↔ (formula_1418 c1_node c1_sign c2_node)) ↔ ((shared_expr_Repair050_8 c1_node c1_sign c2_node) ↔ ((shared_expr_Repair050_68 c1_node c1_sign c2_node) ∨ (shared_expr_Repair050_69 c1_node c2_node))) := (iff_congr (normalization_4938 c1_node c1_sign c2_node) (normalization_5033 c1_node c1_sign c2_node))

-- Checked replay of monotonicity.
theorem replay_2856 (c1_node c1_sign c2_node : Int) : ((formula_1400 c1_node c1_sign c2_node) ↔ (formula_1418 c1_node c1_sign c2_node)) := by
  classical
  have ht := (normalized_1180 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))) (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Repair050_64 c1_node c2_node) := by
    exact Iff.mp (normalization_5032 c1_node c2_node) (replay_2855 c1_node c2_node)
  have n1 : ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_5003 c1_sign) (replay_2843 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5034 c1_node c1_sign c2_node) hn

theorem normalized_1181 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair050_70 (c1_node c2_node : Int) : Prop := (((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_5035 (c1_node c1_sign c2_node : Int) : (formula_1377 c1_node c1_sign c2_node) ↔ ((shared_expr_Repair050_70 c1_node c2_node) ∨ (shared_expr_Repair050_68 c1_node c1_sign c2_node)) := (or_congr (and_congr (normalization_5029 c1_node c2_node) (normalization_4937 c1_node c2_node)) (and_congr (not_congr (normalization_5029 c1_node c2_node)) (normalization_1802 c1_sign)))

theorem normalization_5036 (c1_node c1_sign c2_node : Int) : ((formula_1418 c1_node c1_sign c2_node) ↔ (formula_1377 c1_node c1_sign c2_node)) ↔ (((shared_expr_Repair050_68 c1_node c1_sign c2_node) ∨ (shared_expr_Repair050_69 c1_node c2_node)) ↔ ((shared_expr_Repair050_70 c1_node c2_node) ∨ (shared_expr_Repair050_68 c1_node c1_sign c2_node))) := (iff_congr (normalization_5033 c1_node c1_sign c2_node) (normalization_5035 c1_node c1_sign c2_node))

-- Checked replay of rewrite.
theorem replay_2857 (c1_node c1_sign c2_node : Int) : ((formula_1418 c1_node c1_sign c2_node) ↔ (formula_1377 c1_node c1_sign c2_node)) := by
  classical
  have ht := (normalized_1181 ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))) (((c2_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5036 c1_node c1_sign c2_node) hn

theorem normalized_1182 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5037 (c1_node c1_sign c2_node : Int) : ((formula_1400 c1_node c1_sign c2_node) ↔ (formula_1377 c1_node c1_sign c2_node)) ↔ ((shared_expr_Repair050_8 c1_node c1_sign c2_node) ↔ ((shared_expr_Repair050_70 c1_node c2_node) ∨ (shared_expr_Repair050_68 c1_node c1_sign c2_node))) := (iff_congr (normalization_4938 c1_node c1_sign c2_node) (normalization_5035 c1_node c1_sign c2_node))

-- Checked replay of trans.
theorem replay_2858 (c1_node c1_sign c2_node : Int) : ((formula_1400 c1_node c1_sign c2_node) ↔ (formula_1377 c1_node c1_sign c2_node)) := by
  classical
  have ht := (normalized_1182 (shared_expr_Repair050_8 c1_node c1_sign c2_node) ((shared_expr_Repair050_68 c1_node c1_sign c2_node) ∨ (shared_expr_Repair050_69 c1_node c2_node)) ((shared_expr_Repair050_70 c1_node c2_node) ∨ (shared_expr_Repair050_68 c1_node c1_sign c2_node)))
  have n0 : ((shared_expr_Repair050_8 c1_node c1_sign c2_node) ↔ ((shared_expr_Repair050_68 c1_node c1_sign c2_node) ∨ (shared_expr_Repair050_69 c1_node c2_node))) := by
    exact Iff.mp (normalization_5034 c1_node c1_sign c2_node) (replay_2856 c1_node c1_sign c2_node)
  have n1 : (((shared_expr_Repair050_68 c1_node c1_sign c2_node) ∨ (shared_expr_Repair050_69 c1_node c2_node)) ↔ ((shared_expr_Repair050_70 c1_node c2_node) ∨ (shared_expr_Repair050_68 c1_node c1_sign c2_node))) := by
    exact Iff.mp (normalization_5036 c1_node c1_sign c2_node) (replay_2857 c1_node c1_sign c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5037 c1_node c1_sign c2_node) hn

theorem normalized_1183 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5038 (c1_depth c2_depth : Int) : ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ↔ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_5039 (c1_depth c2_depth : Int) : ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_5040 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := (and_congr (normalization_5038 c1_depth c2_depth) (normalization_5039 c1_depth c2_depth))

abbrev shared_expr_Repair050_71 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))
theorem normalization_5041 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Repair050_71 c1_depth c2_depth) := (iff_congr (normalization_4939 c1_depth c2_depth) (normalization_5040 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2859 (c1_depth c2_depth : Int) : (((c1_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1183 (((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5041 c1_depth c2_depth) hn

abbrev shared_expr_Repair050_72 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))
abbrev formula_1419 (c1_depth c2_depth : Int) : Prop := (shared_expr_Repair050_72 c1_depth c2_depth)

theorem normalized_1184 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5042 (c1_depth c2_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) := (not_congr (normalization_5038 c1_depth c2_depth))

theorem normalization_5043 (c1_depth c2_depth : Int) : (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := (not_congr (normalization_5039 c1_depth c2_depth))

theorem normalization_5044 (c1_depth c2_depth : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) := (or_congr (normalization_5042 c1_depth c2_depth) (normalization_5043 c1_depth c2_depth))

theorem normalization_5045 (c1_depth c2_depth : Int) : (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) := (not_congr (normalization_5044 c1_depth c2_depth))

abbrev shared_expr_Repair050_73 (c1_depth c2_depth : Int) : Prop := ((((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))))
theorem normalization_5046 (c1_depth c2_depth : Int) : (formula_1419 c1_depth c2_depth) ↔ (shared_expr_Repair050_73 c1_depth c2_depth) := (iff_congr (normalization_5040 c1_depth c2_depth) (normalization_5045 c1_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2860 (c1_depth c2_depth : Int) : (formula_1419 c1_depth c2_depth) := by
  classical
  have ht := (normalized_1184 ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5046 c1_depth c2_depth) hn

end H4Formal.Generated.Repair
