import H4Formal.Certificates.CheckedClassification.Classification080

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_5094 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2197 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_5093 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) i290

abbrev shared_expr_Classification081_0 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2197 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2197 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2199 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_0 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1867 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification081_1 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (((((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification081_2 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification081_1 c2_group c2_mode c3_group c3_mode)) ∨ ((¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification081_3 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification081_2 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
abbrev shared_expr_Classification081_4 (c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
abbrev shared_expr_Classification081_5 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification081_6 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification081_5 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification081_7 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification081_8 (c2_node c2_sign c3_node : Int) : Prop := ((((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_7 c2_node c3_node))
abbrev shared_expr_Classification081_9 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification081_10 (c2_node c3_node c3_sign : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification081_9 c2_node c3_node))
abbrev shared_expr_Classification081_11 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Classification081_10 c2_node c3_node c3_sign)))
abbrev shared_expr_Classification081_12 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification081_8 c2_node c2_sign c3_node)) ∨ (shared_expr_Classification081_11 c2_depth c2_node c3_depth c3_node c3_sign))
abbrev shared_expr_Classification081_13 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification081_12 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
abbrev shared_expr_Classification081_14 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification081_6 c2_node c2_sign c3_node c3_sign)) ∨ (shared_expr_Classification081_13 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
abbrev shared_expr_Classification081_15 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification081_14 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev shared_expr_Classification081_16 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) ∨ (shared_expr_Classification081_15 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
abbrev shared_expr_Classification081_17 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification081_16 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev shared_expr_Classification081_18 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification081_4 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Classification081_17 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
abbrev shared_expr_Classification081_19 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification081_18 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification081_18 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
theorem normalization_7229 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2199 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification081_19 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_7227 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_7227 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5095 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2199 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1867 (shared_expr_Classification081_18 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7229 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

-- Checked replay of mp.
theorem replay_5096 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2197 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_5095 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_5094 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i290)

abbrev shared_expr_Classification081_20 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((c2_level = c3_level) ∧ (((c2_mode = c3_mode) ∧ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ∨ ((¬ (c2_level = c3_level)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))
abbrev formula_2200 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (shared_expr_Classification081_20 c2_group c2_level c2_mode c3_group c3_level c3_mode)

abbrev shared_expr_Classification081_21 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2200 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))))
abbrev formula_2201 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((¬ (c3_kind = (0 : Int))) ∨ (shared_expr_Classification081_21 c2_group c2_level c2_mode c3_group c3_level c3_mode))

abbrev shared_expr_Classification081_22 (c2_node c2_sign c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ∧ (c2_sign = (0 : Int))) ∨ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))))
abbrev formula_2202 (c2_node c2_sign c3_node : Int) : Prop := (shared_expr_Classification081_22 c2_node c2_sign c3_node)

abbrev shared_expr_Classification081_23 (c2_node c3_node c3_sign : Int) : Prop := ((((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ∧ (c3_sign = (1 : Int))) ∨ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_2203 (c2_node c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_23 c2_node c3_node c3_sign)

abbrev shared_expr_Classification081_24 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ∧ (formula_2202 c2_node c2_sign c3_node)) ∨ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int))) ∧ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_2203 c2_node c3_node c3_sign))))
abbrev formula_2204 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_24 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Classification081_25 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((c2_depth = c3_depth) ∧ (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ∨ ((¬ (c2_depth = c3_depth)) ∧ (formula_2204 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev formula_2205 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_25 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Classification081_26 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (c3_kind = (0 : Int))) ∧ (((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev formula_2206 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_26 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Classification081_27 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((c2_kind = (0 : Int)) ∧ (formula_2201 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_2206 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev formula_2207 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_27 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Classification081_28 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2197 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2207 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2208 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_28 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1868 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ ((¬ p10) ∧ p11)) ∨ p12))))))))))) ↔ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ (p11 ∧ (¬ p10))) ∨ p12)))))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7230 (c2_group c3_group : Int) : ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)) ↔ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7231 (c2_group c3_group : Int) : (¬ ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_7230 c2_group c3_group))

theorem normalization_7232 (c2_mode c3_mode : Int) : ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)) ↔ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7233 (c2_mode c3_mode : Int) : (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_7232 c2_mode c3_mode))

theorem normalization_7234 (c2_group c2_mode c3_group c3_mode : Int) : (((c2_mode = c3_mode) ∧ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ↔ (shared_expr_Classification081_1 c2_group c2_mode c3_group c3_mode) := (or_congr (and_congr (normalization_7197 c2_mode c3_mode) (normalization_7231 c2_group c3_group)) (and_congr (not_congr (normalization_7197 c2_mode c3_mode)) (normalization_7233 c2_mode c3_mode)))

theorem normalization_7235 (c2_level c3_level : Int) : ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ↔ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7236 (c2_level c3_level : Int) : (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_7235 c2_level c3_level))

theorem normalization_7237 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2200 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification081_2 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7196 c2_level c3_level) (normalization_7234 c2_group c2_mode c3_group c3_mode)) (and_congr (not_congr (normalization_7196 c2_level c3_level)) (normalization_7236 c2_level c3_level)))

theorem normalization_7238 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (shared_expr_Classification081_21 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7195 c2_mode c3_mode) (normalization_7237 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_7195 c2_mode c3_mode)) (normalization_1287 c2_mode)))

theorem normalization_7239 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2201 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (or_congr (normalization_7194 c3_kind) (normalization_7238 c2_group c2_level c2_mode c3_group c3_level c3_mode))

theorem normalization_7240 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7241 (c2_node c3_node : Int) : (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7240 c2_node c3_node))

theorem normalization_7242 (c2_node c2_sign c3_node c3_sign : Int) : (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (shared_expr_Classification081_6 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_7175 c2_node c3_node) (normalization_7176 c2_sign c3_sign)) (and_congr (not_congr (normalization_7175 c2_node c3_node)) (normalization_7241 c2_node c3_node)))

theorem normalization_7243 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_7244 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_7245 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7246 (c2_node c3_node : Int) : (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_7245 c2_node c3_node))

theorem normalization_7247 (c2_node c2_sign c3_node : Int) : (formula_2202 c2_node c2_sign c3_node) ↔ (shared_expr_Classification081_8 c2_node c2_sign c3_node) := (or_congr (and_congr (normalization_7244 c2_node c3_node) (normalization_662 c2_sign)) (and_congr (not_congr (normalization_7244 c2_node c3_node)) (normalization_7246 c2_node c3_node)))

theorem normalization_7248 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := by
  omega

theorem normalization_7249 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) := (not_congr (normalization_7248 c2_depth c3_depth))

theorem normalization_7250 (c2_node c3_node : Int) : ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_7251 (c2_node c3_node : Int) : ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7252 (c2_node c3_node : Int) : (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7251 c2_node c3_node))

theorem normalization_7253 (c2_node c3_node c3_sign : Int) : (formula_2203 c2_node c3_node c3_sign) ↔ (shared_expr_Classification081_10 c2_node c3_node c3_sign) := (or_congr (and_congr (normalization_7250 c2_node c3_node) (normalization_6554 c3_sign)) (and_congr (not_congr (normalization_7250 c2_node c3_node)) (normalization_7252 c2_node c3_node)))

theorem normalization_7254 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_2203 c2_node c3_node c3_sign)) ↔ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification081_10 c2_node c3_node c3_sign)) := (or_congr (normalization_7249 c2_depth c3_depth) (normalization_7253 c2_node c3_node c3_sign))

abbrev shared_expr_Classification081_29 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification081_10 c2_node c3_node c3_sign)))
abbrev shared_expr_Classification081_30 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification081_8 c2_node c2_sign c3_node)) ∨ (shared_expr_Classification081_29 c2_depth c2_node c3_depth c3_node c3_sign))
theorem normalization_7255 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2204 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification081_30 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7243 c2_depth c3_depth) (normalization_7247 c2_node c2_sign c3_node)) (and_congr (not_congr (normalization_7243 c2_depth c3_depth)) (normalization_7254 c2_depth c2_node c3_depth c3_node c3_sign)))

abbrev shared_expr_Classification081_31 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification081_30 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
abbrev shared_expr_Classification081_32 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification081_6 c2_node c2_sign c3_node c3_sign)) ∨ (shared_expr_Classification081_31 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
theorem normalization_7256 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification081_32 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7174 c2_depth c3_depth) (normalization_7242 c2_node c2_sign c3_node c3_sign)) (and_congr (not_congr (normalization_7174 c2_depth c3_depth)) (normalization_7255 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

theorem normalization_7257 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : ((¬ (c3_kind = (2 : Int))) ∧ (formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification081_32 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (and_congr (normalization_7208 c3_kind) (normalization_7256 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

abbrev shared_expr_Classification081_33 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification081_32 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev shared_expr_Classification081_34 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) ∨ (shared_expr_Classification081_33 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7258 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2205 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))) ↔ (shared_expr_Classification081_34 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_659 c2_kind) (normalization_6546 c3_kind)) (and_congr (not_congr (normalization_659 c2_kind)) (normalization_7257 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

theorem normalization_7259 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2206 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification081_34 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := (and_congr (normalization_7194 c3_kind) (normalization_7258 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

abbrev shared_expr_Classification081_35 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification081_34 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev shared_expr_Classification081_36 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification081_4 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Classification081_35 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7260 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2207 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification081_36 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (or_congr (and_congr (normalization_652 c2_kind) (normalization_7239 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) (and_congr (not_congr (normalization_652 c2_kind)) (normalization_7259 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Classification081_37 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification081_18 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification081_36 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
theorem normalization_7261 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2208 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification081_37 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_7227 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_7260 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5097 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2208 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1868 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Classification081_6 c2_node c2_sign c3_node c3_sign) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Classification081_8 c2_node c2_sign c3_node) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) (shared_expr_Classification081_10 c2_node c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7261 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

-- Checked replay of mp.
theorem replay_5098 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i290 : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2207 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_5097 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_5096 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i290)

theorem normalized_1869 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7262 (c3_kind : Int) : (¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := (not_congr (normalization_6746 c3_kind))

theorem normalization_7263 (c3_kind : Int) : ((¬ (c3_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))))) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))))) := (iff_congr (normalization_7194 c3_kind) (normalization_7262 c3_kind))

-- Checked replay of monotonicity.
theorem replay_5099 (c3_kind : Int) : ((¬ (c3_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1869 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))
  have n0 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6748 c3_kind) (replay_4923 c3_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_7263 c3_kind) hn

theorem normalized_1870 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7264 (c3_kind : Int) : ((¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ↔ ((¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_7262 c3_kind) (normalization_6745 c3_kind))

-- Checked replay of rewrite.
theorem replay_5100 (c3_kind : Int) : ((¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1870 ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_7264 c3_kind) hn

theorem normalized_1871 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7265 (c3_kind : Int) : ((¬ (c3_kind = (0 : Int))) ↔ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_7194 c3_kind) (normalization_6745 c3_kind))

-- Checked replay of trans.
theorem replay_5101 (c3_kind : Int) : ((¬ (c3_kind = (0 : Int))) ↔ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1871 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))
  have n0 : ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))))) := by
    exact Iff.mp (normalization_7263 c3_kind) (replay_5099 c3_kind)
  have n1 : ((¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_7264 c3_kind) (replay_5100 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7265 c3_kind) hn

abbrev shared_expr_Classification081_38 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2183 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))))
abbrev formula_2209 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((shared_expr_Classification081_21 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification081_38 c2_group c2_level c2_mode c3_group c3_level c3_mode))

theorem normalized_1872 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7266 (c2_level c3_level : Int) : ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_7267 (c2_level c3_level : Int) : (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) := (not_congr (normalization_7266 c2_level c3_level))

theorem normalization_7268 (c2_level c3_level : Int) : ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) := (or_congr (normalization_7267 c2_level c3_level) (normalization_7236 c2_level c3_level))

theorem normalization_7269 (c2_mode c3_mode : Int) : ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_7270 (c2_mode c3_mode : Int) : (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) := (not_congr (normalization_7269 c2_mode c3_mode))

theorem normalization_7271 (c2_mode c3_mode : Int) : ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_7270 c2_mode c3_mode) (normalization_7233 c2_mode c3_mode))

abbrev shared_expr_Classification081_39 (c2_group c2_mode c3_group c3_mode : Int) : Prop := ((((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))))
theorem normalization_7272 (c2_group c2_mode c3_group c3_mode : Int) : (formula_2182 c2_group c2_mode c3_group c3_mode) ↔ (shared_expr_Classification081_39 c2_group c2_mode c3_group c3_mode) := (or_congr (and_congr (normalization_7271 c2_mode c3_mode) (normalization_7233 c2_mode c3_mode)) (and_congr (not_congr (normalization_7271 c2_mode c3_mode)) (normalization_7231 c2_group c3_group)))

abbrev shared_expr_Classification081_40 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification081_39 c2_group c2_mode c3_group c3_mode)))
theorem normalization_7273 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2183 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification081_40 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7268 c2_level c3_level) (normalization_7236 c2_level c3_level)) (and_congr (not_congr (normalization_7268 c2_level c3_level)) (normalization_7272 c2_group c2_mode c3_group c3_mode)))

abbrev shared_expr_Classification081_41 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification081_40 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
theorem normalization_7274 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (shared_expr_Classification081_38 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7195 c2_mode c3_mode) (normalization_7273 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_7195 c2_mode c3_mode)) (normalization_1287 c2_mode)))

theorem normalization_7275 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2209 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ ((shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (iff_congr (normalization_7238 c2_group c2_level c2_mode c3_group c3_level c3_mode) (normalization_7274 c2_group c2_level c2_mode c3_group c3_level c3_mode))

-- Checked replay of rewrite.
theorem replay_5102 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2209 c2_group c2_level c2_mode c3_group c3_level c3_mode) := by
  classical
  have ht := (normalized_1872 ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)) ((c2_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7275 c2_group c2_level c2_mode c3_group c3_level c3_mode) hn

abbrev formula_2210 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ∨ (shared_expr_Classification081_38 c2_group c2_level c2_mode c3_group c3_level c3_mode))

theorem normalized_1873 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7276 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2210 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6745 c3_kind) (normalization_7274 c2_group c2_level c2_mode c3_group c3_level c3_mode))

abbrev shared_expr_Classification081_42 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem normalization_7277 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2201 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2210 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification081_42 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_7239 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (normalization_7276 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of monotonicity.
theorem replay_5103 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2201 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2210 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_1873 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode) (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode))
  have n0 : ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_7265 c3_kind) (replay_5101 c3_kind)
  have n1 : ((shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := by
    exact Iff.mp (normalization_7275 c2_group c2_level c2_mode c3_group c3_level c3_mode) (replay_5102 c2_group c2_level c2_mode c3_group c3_level c3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7277 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_1874 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7278 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2184 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6743 c3_kind) (or_congr (normalization_6744 c3_kind) (normalization_7274 c2_group c2_level c2_mode c3_group c3_level c3_mode)))

abbrev shared_expr_Classification081_43 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem normalization_7279 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2210 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2184 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification081_43 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_7276 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (normalization_7278 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of rewrite.
theorem replay_5104 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2210 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2184 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_1874 ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)) (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode))
  have hn := ht
  exact Iff.mpr (normalization_7279 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_1875 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification081_44 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem normalization_7280 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2201 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2184 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification081_44 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_7239 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (normalization_7278 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of trans.
theorem replay_5105 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2201 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2184 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_1875 ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification081_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
  have n0 : (shared_expr_Classification081_42 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_7277 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (replay_5103 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)
  have n1 : (shared_expr_Classification081_43 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_7279 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (replay_5104 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7280 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_1876 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7281 (c3_kind : Int) : ((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int))) ↔ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) := (and_congr (normalization_6810 c3_kind) (normalization_6812 c3_kind))

theorem normalization_7282 (c3_kind : Int) : ((c3_kind = (1 : Int)) ↔ ((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int)))) ↔ ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) := (iff_congr (normalization_6546 c3_kind) (normalization_7281 c3_kind))

-- Checked replay of rewrite.
theorem replay_5106 (c3_kind : Int) : ((c3_kind = (1 : Int)) ↔ ((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1876 (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7282 c3_kind) hn

theorem normalized_1877 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7283 (c3_kind : Int) : ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))) ↔ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) := (or_congr (normalization_6811 c3_kind) (normalization_6813 c3_kind))

theorem normalization_7284 (c3_kind : Int) : (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))))) := (not_congr (normalization_7283 c3_kind))

theorem normalization_7285 (c3_kind : Int) : (((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) ↔ ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_7281 c3_kind) (normalization_7284 c3_kind))

-- Checked replay of rewrite.
theorem replay_5107 (c3_kind : Int) : (((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1877 ((c3_kind) ≤ (1 : Int)) ((c3_kind) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7285 c3_kind) hn

theorem normalized_1878 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7286 (c3_kind : Int) : ((c3_kind = (1 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) ↔ ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_6546 c3_kind) (normalization_7284 c3_kind))

-- Checked replay of trans.
theorem replay_5108 (c3_kind : Int) : ((c3_kind = (1 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1878 (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))))
  have n0 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_7282 c3_kind) (replay_5106 c3_kind)
  have n1 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_7285 c3_kind) (replay_5107 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7286 c3_kind) hn

theorem normalized_1879 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7287 (c3_kind : Int) : (¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := (not_congr (normalization_6839 c3_kind))

theorem normalization_7288 (c3_kind : Int) : ((¬ (c3_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))))) ↔ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))))) := (iff_congr (normalization_7208 c3_kind) (normalization_7287 c3_kind))

-- Checked replay of monotonicity.
theorem replay_5109 (c3_kind : Int) : ((¬ (c3_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_1879 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))
  have n0 : ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6900 c3_kind) (replay_4958 c3_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_7288 c3_kind) hn

theorem normalized_1880 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7289 (c3_kind : Int) : ((¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ↔ ((¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_7287 c3_kind) (normalization_6838 c3_kind))

-- Checked replay of rewrite.
theorem replay_5110 (c3_kind : Int) : ((¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_1880 ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_7289 c3_kind) hn

theorem normalized_1881 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7290 (c3_kind : Int) : ((¬ (c3_kind = (2 : Int))) ↔ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ↔ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_7208 c3_kind) (normalization_6838 c3_kind))

-- Checked replay of trans.
theorem replay_5111 (c3_kind : Int) : ((¬ (c3_kind = (2 : Int))) ↔ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_1881 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))
  have n0 : ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_7288 c3_kind) (replay_5109 c3_kind)
  have n1 : ((¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_7289 c3_kind) (replay_5110 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7290 c3_kind) hn

theorem normalized_1882 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7291 (c2_depth c3_depth : Int) : (c2_depth ≤ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_7292 (c2_depth c3_depth : Int) : (c2_depth ≥ c3_depth) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7293 (c2_depth c3_depth : Int) : ((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_7291 c2_depth c3_depth) (normalization_7292 c2_depth c3_depth))

abbrev shared_expr_Classification081_45 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
theorem normalization_7294 (c2_depth c3_depth : Int) : ((c2_depth = c3_depth) ↔ ((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth))) ↔ (shared_expr_Classification081_45 c2_depth c3_depth) := (iff_congr (normalization_7174 c2_depth c3_depth) (normalization_7293 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5112 (c2_depth c3_depth : Int) : ((c2_depth = c3_depth) ↔ ((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth))) := by
  classical
  have ht := (normalized_1882 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7294 c2_depth c3_depth) hn

theorem normalized_1883 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7295 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_7296 (c2_depth c3_depth : Int) : ((c2_depth ≤ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := (iff_congr (normalization_7291 c2_depth c3_depth) (normalization_7295 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5113 (c2_depth c3_depth : Int) : ((c2_depth ≤ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1883 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7296 c2_depth c3_depth) hn

theorem normalized_1884 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7297 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7298 (c2_depth c3_depth : Int) : ((c2_depth ≥ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_7292 c2_depth c3_depth) (normalization_7297 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5114 (c2_depth c3_depth : Int) : ((c2_depth ≥ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1884 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7298 c2_depth c3_depth) hn

theorem normalized_1885 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7299 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_7295 c2_depth c3_depth) (normalization_7297 c2_depth c3_depth))

theorem normalization_7300 (c2_depth c3_depth : Int) : (((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification081_45 c2_depth c3_depth) := (iff_congr (normalization_7293 c2_depth c3_depth) (normalization_7299 c2_depth c3_depth))

-- Checked replay of monotonicity.
theorem replay_5115 (c2_depth c3_depth : Int) : (((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1885 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
  have n0 : (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_7296 c2_depth c3_depth) (replay_5113 c2_depth c3_depth)
  have n1 : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_7298 c2_depth c3_depth) (replay_5114 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7300 c2_depth c3_depth) hn

abbrev shared_expr_Classification081_46 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))))
abbrev formula_2211 (c2_depth c3_depth : Int) : Prop := (shared_expr_Classification081_46 c2_depth c3_depth)

theorem normalized_1886 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7301 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := (not_congr (normalization_7295 c2_depth c3_depth))

theorem normalization_7302 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_7297 c2_depth c3_depth))

theorem normalization_7303 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_7301 c2_depth c3_depth) (normalization_7302 c2_depth c3_depth))

theorem normalization_7304 (c2_depth c3_depth : Int) : (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_7303 c2_depth c3_depth))

abbrev shared_expr_Classification081_47 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))))
theorem normalization_7305 (c2_depth c3_depth : Int) : (formula_2211 c2_depth c3_depth) ↔ (shared_expr_Classification081_47 c2_depth c3_depth) := (iff_congr (normalization_7299 c2_depth c3_depth) (normalization_7304 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5116 (c2_depth c3_depth : Int) : (formula_2211 c2_depth c3_depth) := by
  classical
  have ht := (normalized_1886 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7305 c2_depth c3_depth) hn

theorem normalized_1887 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7306 (c2_depth c3_depth : Int) : (((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification081_47 c2_depth c3_depth) := (iff_congr (normalization_7293 c2_depth c3_depth) (normalization_7304 c2_depth c3_depth))

-- Checked replay of trans.
theorem replay_5117 (c2_depth c3_depth : Int) : (((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1887 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Classification081_47 c2_depth c3_depth))
  have n0 : (shared_expr_Classification081_45 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7300 c2_depth c3_depth) (replay_5115 c2_depth c3_depth)
  have n1 : (shared_expr_Classification081_47 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7305 c2_depth c3_depth) (replay_5116 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7306 c2_depth c3_depth) hn

theorem normalized_1888 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7307 (c2_depth c3_depth : Int) : ((c2_depth = c3_depth) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification081_47 c2_depth c3_depth) := (iff_congr (normalization_7174 c2_depth c3_depth) (normalization_7304 c2_depth c3_depth))

-- Checked replay of trans.
theorem replay_5118 (c2_depth c3_depth : Int) : ((c2_depth = c3_depth) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1888 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Classification081_47 c2_depth c3_depth))
  have n0 : (shared_expr_Classification081_45 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7294 c2_depth c3_depth) (replay_5112 c2_depth c3_depth)
  have n1 : (shared_expr_Classification081_47 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7306 c2_depth c3_depth) (replay_5117 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7307 c2_depth c3_depth) hn

theorem normalized_1889 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7308 (c2_node c3_node : Int) : (c2_node ≤ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7309 (c2_node c3_node : Int) : (c2_node ≥ c3_node) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7310 (c2_node c3_node : Int) : ((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_7308 c2_node c3_node) (normalization_7309 c2_node c3_node))

abbrev shared_expr_Classification081_48 (c2_node c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_7311 (c2_node c3_node : Int) : ((c2_node = c3_node) ↔ ((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node))) ↔ (shared_expr_Classification081_48 c2_node c3_node) := (iff_congr (normalization_7175 c2_node c3_node) (normalization_7310 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_5119 (c2_node c3_node : Int) : ((c2_node = c3_node) ↔ ((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node))) := by
  classical
  have ht := (normalized_1889 (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7311 c2_node c3_node) hn

theorem normalized_1890 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7312 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7313 (c2_node c3_node : Int) : ((c2_node ≤ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (iff_congr (normalization_7308 c2_node c3_node) (normalization_7312 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_5120 (c2_node c3_node : Int) : ((c2_node ≤ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1890 ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7313 c2_node c3_node) hn

theorem normalized_1891 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7314 (c2_node c3_node : Int) : ((c2_node ≥ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_7309 c2_node c3_node) (normalization_7240 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_5121 (c2_node c3_node : Int) : ((c2_node ≥ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1891 ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7314 c2_node c3_node) hn

theorem normalized_1892 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7315 (c2_node c3_node : Int) : (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_7312 c2_node c3_node) (normalization_7240 c2_node c3_node))

theorem normalization_7316 (c2_node c3_node : Int) : (((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification081_48 c2_node c3_node) := (iff_congr (normalization_7310 c2_node c3_node) (normalization_7315 c2_node c3_node))

-- Checked replay of monotonicity.
theorem replay_5122 (c2_node c3_node : Int) : (((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1892 ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have n0 : (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_7313 c2_node c3_node) (replay_5120 c2_node c3_node)
  have n1 : ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_7314 c2_node c3_node) (replay_5121 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7316 c2_node c3_node) hn

abbrev shared_expr_Classification081_49 (c2_node c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))))
abbrev formula_2212 (c2_node c3_node : Int) : Prop := (shared_expr_Classification081_49 c2_node c3_node)

theorem normalized_1893 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7317 (c2_node c3_node : Int) : (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_7312 c2_node c3_node))

theorem normalization_7318 (c2_node c3_node : Int) : ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_7317 c2_node c3_node) (normalization_7241 c2_node c3_node))

theorem normalization_7319 (c2_node c3_node : Int) : (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_7318 c2_node c3_node))

abbrev shared_expr_Classification081_50 (c2_node c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))))
theorem normalization_7320 (c2_node c3_node : Int) : (formula_2212 c2_node c3_node) ↔ (shared_expr_Classification081_50 c2_node c3_node) := (iff_congr (normalization_7315 c2_node c3_node) (normalization_7319 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_5123 (c2_node c3_node : Int) : (formula_2212 c2_node c3_node) := by
  classical
  have ht := (normalized_1893 ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7320 c2_node c3_node) hn

theorem normalized_1894 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7321 (c2_node c3_node : Int) : (((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification081_50 c2_node c3_node) := (iff_congr (normalization_7310 c2_node c3_node) (normalization_7319 c2_node c3_node))

-- Checked replay of trans.
theorem replay_5124 (c2_node c3_node : Int) : (((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1894 (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Classification081_50 c2_node c3_node))
  have n0 : (shared_expr_Classification081_48 c2_node c3_node) := by
    exact Iff.mp (normalization_7316 c2_node c3_node) (replay_5122 c2_node c3_node)
  have n1 : (shared_expr_Classification081_50 c2_node c3_node) := by
    exact Iff.mp (normalization_7320 c2_node c3_node) (replay_5123 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7321 c2_node c3_node) hn

theorem normalized_1895 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7322 (c2_node c3_node : Int) : ((c2_node = c3_node) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification081_50 c2_node c3_node) := (iff_congr (normalization_7175 c2_node c3_node) (normalization_7319 c2_node c3_node))

-- Checked replay of trans.
theorem replay_5125 (c2_node c3_node : Int) : ((c2_node = c3_node) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1895 (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Classification081_50 c2_node c3_node))
  have n0 : (shared_expr_Classification081_48 c2_node c3_node) := by
    exact Iff.mp (normalization_7311 c2_node c3_node) (replay_5119 c2_node c3_node)
  have n1 : (shared_expr_Classification081_50 c2_node c3_node) := by
    exact Iff.mp (normalization_7321 c2_node c3_node) (replay_5124 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7322 c2_node c3_node) hn

theorem normalized_1896 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7323 (c2_sign c3_sign : Int) : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (and_congr (normalization_976 c2_sign) (normalization_6849 c3_sign))

abbrev shared_expr_Classification081_51 (c2_sign c3_sign : Int) : Prop := (((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))))
theorem normalization_7324 (c2_sign c3_sign : Int) : (((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) ↔ (shared_expr_Classification081_51 c2_sign c3_sign) := (iff_congr (normalization_7176 c2_sign c3_sign) (normalization_7323 c2_sign c3_sign))

-- Checked replay of monotonicity.
theorem replay_5126 (c2_sign c3_sign : Int) : (((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_1896 (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1114 c2_sign) (replay_519 c2_sign)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6942 c3_sign) (replay_4980 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7324 c2_sign c3_sign) hn

abbrev shared_expr_Classification081_52 (c2_sign c3_sign : Int) : Prop := (((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev formula_2213 (c2_sign c3_sign : Int) : Prop := (shared_expr_Classification081_52 c2_sign c3_sign)

theorem normalized_1897 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7325 (c2_sign c3_sign : Int) : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ↔ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) := (or_congr (normalization_972 c2_sign) (or_congr (normalization_974 c2_sign) (or_congr (normalization_6845 c3_sign) (normalization_6847 c3_sign))))

theorem normalization_7326 (c2_sign c3_sign : Int) : (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_7325 c2_sign c3_sign))

abbrev shared_expr_Classification081_53 (c2_sign c3_sign : Int) : Prop := (((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_7327 (c2_sign c3_sign : Int) : (formula_2213 c2_sign c3_sign) ↔ (shared_expr_Classification081_53 c2_sign c3_sign) := (iff_congr (normalization_7323 c2_sign c3_sign) (normalization_7326 c2_sign c3_sign))

-- Checked replay of rewrite.
theorem replay_5127 (c2_sign c3_sign : Int) : (formula_2213 c2_sign c3_sign) := by
  classical
  have ht := (normalized_1897 ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7327 c2_sign c3_sign) hn

theorem normalized_1898 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification081_54 (c2_sign c3_sign : Int) : Prop := (((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_7328 (c2_sign c3_sign : Int) : (((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (shared_expr_Classification081_54 c2_sign c3_sign) := (iff_congr (normalization_7176 c2_sign c3_sign) (normalization_7326 c2_sign c3_sign))

-- Checked replay of trans.
theorem replay_5128 (c2_sign c3_sign : Int) : (((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1898 ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification081_51 c2_sign c3_sign) := by
    exact Iff.mp (normalization_7324 c2_sign c3_sign) (replay_5126 c2_sign c3_sign)
  have n1 : (shared_expr_Classification081_53 c2_sign c3_sign) := by
    exact Iff.mp (normalization_7327 c2_sign c3_sign) (replay_5127 c2_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7328 c2_sign c3_sign) hn

abbrev shared_expr_Classification081_55 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification081_56 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification081_55 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))
abbrev formula_2214 (c2_node c2_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_56 c2_node c2_sign c3_node c3_sign)

abbrev shared_expr_Classification081_57 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_2214 c2_node c2_sign c3_node c3_sign))
abbrev formula_2215 (c2_node c2_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_57 c2_node c2_sign c3_node c3_sign)

theorem normalized_1899 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification081_58 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification081_59 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification081_58 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_7329 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2214 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Classification081_59 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_7319 c2_node c3_node) (normalization_7326 c2_sign c3_sign)) (and_congr (not_congr (normalization_7319 c2_node c3_node)) (normalization_7241 c2_node c3_node)))

theorem normalization_7330 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2215 c2_node c2_sign c3_node c3_sign) ↔ ((shared_expr_Classification081_6 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Classification081_59 c2_node c2_sign c3_node c3_sign)) := (iff_congr (normalization_7242 c2_node c2_sign c3_node c3_sign) (normalization_7329 c2_node c2_sign c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_5129 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2215 c2_node c2_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_1899 (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification081_50 c2_node c3_node) := by
    exact Iff.mp (normalization_7322 c2_node c3_node) (replay_5125 c2_node c3_node)
  have n1 : (shared_expr_Classification081_54 c2_sign c3_sign) := by
    exact Iff.mp (normalization_7328 c2_sign c3_sign) (replay_5128 c2_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7330 c2_node c2_sign c3_node c3_sign) hn

theorem normalized_1900 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification081_60 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Classification081_58 c2_node c2_sign c3_node c3_sign))
theorem normalization_7331 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2178 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Classification081_60 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_7318 c2_node c3_node) (normalization_7241 c2_node c3_node)) (and_congr (not_congr (normalization_7318 c2_node c3_node)) (normalization_7326 c2_sign c3_sign)))

theorem normalization_7332 (c2_node c2_sign c3_node c3_sign : Int) : ((formula_2214 c2_node c2_sign c3_node c3_sign) ↔ (formula_2178 c2_node c2_sign c3_node c3_sign)) ↔ ((shared_expr_Classification081_59 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Classification081_60 c2_node c2_sign c3_node c3_sign)) := (iff_congr (normalization_7329 c2_node c2_sign c3_node c3_sign) (normalization_7331 c2_node c2_sign c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5130 (c2_node c2_sign c3_node c3_sign : Int) : ((formula_2214 c2_node c2_sign c3_node c3_sign) ↔ (formula_2178 c2_node c2_sign c3_node c3_sign)) := by
  classical
  have ht := (normalized_1900 ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7332 c2_node c2_sign c3_node c3_sign) hn

abbrev shared_expr_Classification081_61 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_2178 c2_node c2_sign c3_node c3_sign))
abbrev formula_2216 (c2_node c2_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification081_61 c2_node c2_sign c3_node c3_sign)

theorem normalized_1901 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7333 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2216 c2_node c2_sign c3_node c3_sign) ↔ ((shared_expr_Classification081_6 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Classification081_60 c2_node c2_sign c3_node c3_sign)) := (iff_congr (normalization_7242 c2_node c2_sign c3_node c3_sign) (normalization_7331 c2_node c2_sign c3_node c3_sign))

-- Checked replay of trans.
theorem replay_5131 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2216 c2_node c2_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_1901 (shared_expr_Classification081_6 c2_node c2_sign c3_node c3_sign) (shared_expr_Classification081_59 c2_node c2_sign c3_node c3_sign) (shared_expr_Classification081_60 c2_node c2_sign c3_node c3_sign))
  have n0 : ((shared_expr_Classification081_6 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Classification081_59 c2_node c2_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_7330 c2_node c2_sign c3_node c3_sign) (replay_5129 c2_node c2_sign c3_node c3_sign)
  have n1 : ((shared_expr_Classification081_59 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Classification081_60 c2_node c2_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_7332 c2_node c2_sign c3_node c3_sign) (replay_5130 c2_node c2_sign c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7333 c2_node c2_sign c3_node c3_sign) hn

theorem normalized_1902 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7334 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_7335 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_7336 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_7334 c2_depth c3_depth) (normalization_7335 c2_depth c3_depth))

abbrev shared_expr_Classification081_62 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
theorem normalization_7337 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Classification081_62 c2_depth c3_depth) := (iff_congr (normalization_7243 c2_depth c3_depth) (normalization_7336 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5132 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_1902 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7337 c2_depth c3_depth) hn

abbrev shared_expr_Classification081_63 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))))
abbrev formula_2217 (c2_depth c3_depth : Int) : Prop := (shared_expr_Classification081_63 c2_depth c3_depth)

theorem normalized_1903 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7338 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := (not_congr (normalization_7334 c2_depth c3_depth))

theorem normalization_7339 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_7335 c2_depth c3_depth))

theorem normalization_7340 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_7338 c2_depth c3_depth) (normalization_7339 c2_depth c3_depth))

theorem normalization_7341 (c2_depth c3_depth : Int) : (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_7340 c2_depth c3_depth))

abbrev shared_expr_Classification081_64 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))))
theorem normalization_7342 (c2_depth c3_depth : Int) : (formula_2217 c2_depth c3_depth) ↔ (shared_expr_Classification081_64 c2_depth c3_depth) := (iff_congr (normalization_7336 c2_depth c3_depth) (normalization_7341 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_5133 (c2_depth c3_depth : Int) : (formula_2217 c2_depth c3_depth) := by
  classical
  have ht := (normalized_1903 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7342 c2_depth c3_depth) hn

theorem normalized_1904 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7343 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Classification081_64 c2_depth c3_depth) := (iff_congr (normalization_7243 c2_depth c3_depth) (normalization_7341 c2_depth c3_depth))

-- Checked replay of trans.
theorem replay_5134 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_1904 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Classification081_64 c2_depth c3_depth))
  have n0 : (shared_expr_Classification081_62 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7337 c2_depth c3_depth) (replay_5132 c2_depth c3_depth)
  have n1 : (shared_expr_Classification081_64 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7342 c2_depth c3_depth) (replay_5133 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7343 c2_depth c3_depth) hn

theorem normalized_1905 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7344 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7345 (c2_node c3_node : Int) : (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (and_congr (normalization_7344 c2_node c3_node) (normalization_7245 c2_node c3_node))

abbrev shared_expr_Classification081_65 (c2_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_7346 (c2_node c3_node : Int) : (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification081_65 c2_node c3_node) := (iff_congr (normalization_7244 c2_node c3_node) (normalization_7345 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_5135 (c2_node c3_node : Int) : (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1905 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_7346 c2_node c3_node) hn

abbrev shared_expr_Classification081_66 (c2_node c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2218 (c2_node c3_node : Int) : Prop := (shared_expr_Classification081_66 c2_node c3_node)

theorem normalized_1906 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7347 (c2_node c3_node : Int) : (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7344 c2_node c3_node))

theorem normalization_7348 (c2_node c3_node : Int) : ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) := (or_congr (normalization_7347 c2_node c3_node) (normalization_7246 c2_node c3_node))

theorem normalization_7349 (c2_node c3_node : Int) : (¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) := (not_congr (normalization_7348 c2_node c3_node))

abbrev shared_expr_Classification081_67 (c2_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
theorem normalization_7350 (c2_node c3_node : Int) : (formula_2218 c2_node c3_node) ↔ (shared_expr_Classification081_67 c2_node c3_node) := (iff_congr (normalization_7345 c2_node c3_node) (normalization_7349 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_5136 (c2_node c3_node : Int) : (formula_2218 c2_node c3_node) := by
  classical
  have ht := (normalized_1906 (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7350 c2_node c3_node) hn

end H4Formal.Generated.Classification
