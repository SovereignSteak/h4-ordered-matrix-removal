import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair017

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_700 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (formula_610 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_699 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) i62

abbrev shared_expr_Repair018_0 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_610 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_610 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_612 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_0 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_460 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair018_1 (r1_group r1_mode r2_group r2_mode : Int) : Prop := (((((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair018_2 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair018_1 r1_group r1_mode r2_group r2_mode)) ∨ ((¬ (((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair018_3 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair018_2 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))))) ∧ (¬ ((r1_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair018_4 (r1_group r1_kind r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)))
abbrev shared_expr_Repair018_5 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))))
abbrev shared_expr_Repair018_6 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_5 r1_node r1_sign r2_node r2_sign) ∨ ((¬ (((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair018_7 (r1_node r2_node : Int) : Prop := ((¬ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) ∧ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair018_8 (r1_node r1_sign r2_node : Int) : Prop := ((((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∧ (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair018_7 r1_node r2_node))
abbrev shared_expr_Repair018_9 (r1_node r2_node : Int) : Prop := ((¬ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair018_10 (r1_node r2_node r2_sign : Int) : Prop := ((((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_9 r1_node r2_node))
abbrev shared_expr_Repair018_11 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair018_10 r1_node r2_node r2_sign)))
abbrev shared_expr_Repair018_12 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair018_8 r1_node r1_sign r2_node)) ∨ (shared_expr_Repair018_11 r1_depth r1_node r2_depth r2_node r2_sign))
abbrev shared_expr_Repair018_13 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair018_6 r1_node r1_sign r2_node r2_sign)) ∨ ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair018_12 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
abbrev shared_expr_Repair018_14 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ∧ ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair018_13 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
abbrev shared_expr_Repair018_15 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_4 r1_group r1_kind r1_level r1_mode r2_group r2_kind r2_level r2_mode) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair018_14 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))
abbrev shared_expr_Repair018_16 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_15 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_15 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_2532 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_612 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_16 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_2530 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_2530 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_701 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_612 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_460 (shared_expr_Repair018_15 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
  have hn := ht
  exact Iff.mpr (normalization_2532 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

-- Checked replay of mp.
theorem replay_702 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (formula_610 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_701 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_700 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62)

abbrev shared_expr_Repair018_17 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((r1_level = r2_level) ∧ (((r1_mode = r2_mode) ∧ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) ∨ ((¬ (r1_mode = r2_mode)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))))) ∨ ((¬ (r1_level = r2_level)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))))
abbrev formula_613 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair018_17 r1_group r1_level r1_mode r2_group r2_level r2_mode)

abbrev shared_expr_Repair018_18 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((¬ (r2_kind = (0 : Int))) ∨ ((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_613 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))))
abbrev formula_614 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (shared_expr_Repair018_18 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)

abbrev shared_expr_Repair018_19 (r1_node r1_sign r2_node : Int) : Prop := ((((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) = (0 : Int)) ∧ (r1_sign = (1 : Int))) ∨ ((¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))))
abbrev formula_615 (r1_node r1_sign r2_node : Int) : Prop := (shared_expr_Repair018_19 r1_node r1_sign r2_node)

abbrev shared_expr_Repair018_20 (r1_node r2_node r2_sign : Int) : Prop := ((((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) = (0 : Int)) ∧ (r2_sign = (0 : Int))) ∨ ((¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_616 (r1_node r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_20 r1_node r2_node r2_sign)

abbrev shared_expr_Repair018_21 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((((r1_depth + ((-1 : Int) * r2_depth)) = (-1 : Int)) ∧ (formula_615 r1_node r1_sign r2_node)) ∨ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) = (-1 : Int))) ∧ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) = (1 : Int))) ∨ (formula_616 r1_node r2_node r2_sign))))
abbrev formula_617 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_21 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair018_22 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((r1_depth = r2_depth) ∧ (((r1_node = r2_node) ∧ ((r1_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r1_node = r2_node)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))))) ∨ ((¬ (r1_depth = r2_depth)) ∧ (formula_617 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
abbrev formula_618 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_22 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair018_23 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((r1_kind = (0 : Int)) ∧ (formula_614 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) ∨ ((¬ (r1_kind = (0 : Int))) ∧ ((¬ (r2_kind = (0 : Int))) ∧ (¬ (r1_kind = (2 : Int))) ∧ ((r2_kind = (2 : Int)) ∨ (formula_618 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))))
abbrev formula_619 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_23 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Repair018_24 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_610 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_619 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_620 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_24 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_461 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ (¬ p3) ∧ (p4 ∨ ((p5 ∧ p6) ∨ ((¬ p5) ∧ ((p7 ∧ p8) ∨ ((¬ p7) ∧ ((¬ ((¬ p9) ∧ p10)) ∨ p11))))))))) ↔ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ (¬ p3) ∧ (p4 ∨ ((p5 ∧ p6) ∨ ((¬ p5) ∧ ((p7 ∧ p8) ∨ ((¬ p7) ∧ ((¬ (p10 ∧ (¬ p9))) ∨ p11)))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2533 (r1_group r2_group : Int) : ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) ↔ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2534 (r1_group r2_group : Int) : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int))) ↔ (¬ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := (not_congr (normalization_2533 r1_group r2_group))

theorem normalization_2535 (r1_mode r2_mode : Int) : ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)) ↔ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2536 (r1_mode r2_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int))) ↔ (¬ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_2535 r1_mode r2_mode))

theorem normalization_2537 (r1_group r1_mode r2_group r2_mode : Int) : (((r1_mode = r2_mode) ∧ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) ∨ ((¬ (r1_mode = r2_mode)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int))))) ↔ (shared_expr_Repair018_1 r1_group r1_mode r2_group r2_mode) := (or_congr (and_congr (normalization_2501 r1_mode r2_mode) (normalization_2534 r1_group r2_group)) (and_congr (not_congr (normalization_2501 r1_mode r2_mode)) (normalization_2536 r1_mode r2_mode)))

theorem normalization_2538 (r1_level r2_level : Int) : ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)) ↔ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2539 (r1_level r2_level : Int) : (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_2538 r1_level r2_level))

theorem normalization_2540 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_613 r1_group r1_level r1_mode r2_group r2_level r2_mode) ↔ (shared_expr_Repair018_2 r1_group r1_level r1_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_2500 r1_level r2_level) (normalization_2537 r1_group r1_mode r2_group r2_mode)) (and_congr (not_congr (normalization_2500 r1_level r2_level)) (normalization_2539 r1_level r2_level)))

theorem normalization_2541 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : ((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_613 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))) ↔ (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_2499 r1_mode r2_mode) (normalization_2540 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_2499 r1_mode r2_mode)) (normalization_2271 r1_mode)))

theorem normalization_2542 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : (formula_614 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)) := (or_congr (normalization_2498 r2_kind) (normalization_2541 r1_group r1_level r1_mode r2_group r2_level r2_mode))

theorem normalization_2543 (r1_node r2_node : Int) : ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)) ↔ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2544 (r1_node r2_node : Int) : (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))) ↔ (¬ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2543 r1_node r2_node))

theorem normalization_2545 (r1_node r1_sign r2_node r2_sign : Int) : (((r1_node = r2_node) ∧ ((r1_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r1_node = r2_node)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))))) ↔ (shared_expr_Repair018_6 r1_node r1_sign r2_node r2_sign) := (or_congr (and_congr (normalization_2478 r1_node r2_node) (normalization_2480 r1_sign r2_sign)) (and_congr (not_congr (normalization_2478 r1_node r2_node)) (normalization_2544 r1_node r2_node)))

theorem normalization_2546 (r1_depth r2_depth : Int) : ((r1_depth + ((-1 : Int) * r2_depth)) = (-1 : Int)) ↔ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_2547 (r1_node r2_node : Int) : ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2548 (r1_node r2_node : Int) : ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2549 (r1_node r2_node : Int) : (¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := (not_congr (normalization_2548 r1_node r2_node))

theorem normalization_2550 (r1_node r1_sign r2_node : Int) : (formula_615 r1_node r1_sign r2_node) ↔ (shared_expr_Repair018_8 r1_node r1_sign r2_node) := (or_congr (and_congr (normalization_2547 r1_node r2_node) (normalization_2479 r1_sign)) (and_congr (not_congr (normalization_2547 r1_node r2_node)) (normalization_2549 r1_node r2_node)))

theorem normalization_2551 (r1_depth r2_depth : Int) : ((r1_depth + ((-1 : Int) * r2_depth)) = (1 : Int)) ↔ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := by
  omega

theorem normalization_2552 (r1_depth r2_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) = (1 : Int))) ↔ (¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))) := (not_congr (normalization_2551 r1_depth r2_depth))

theorem normalization_2553 (r1_node r2_node : Int) : ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2554 (r1_node r2_node : Int) : ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2555 (r1_node r2_node : Int) : (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2554 r1_node r2_node))

theorem normalization_2556 (r1_node r2_node r2_sign : Int) : (formula_616 r1_node r2_node r2_sign) ↔ (shared_expr_Repair018_10 r1_node r2_node r2_sign) := (or_congr (and_congr (normalization_2553 r1_node r2_node) (normalization_183 r2_sign)) (and_congr (not_congr (normalization_2553 r1_node r2_node)) (normalization_2555 r1_node r2_node)))

theorem normalization_2557 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) = (1 : Int))) ∨ (formula_616 r1_node r2_node r2_sign)) ↔ ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair018_10 r1_node r2_node r2_sign)) := (or_congr (normalization_2552 r1_depth r2_depth) (normalization_2556 r1_node r2_node r2_sign))

abbrev shared_expr_Repair018_25 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair018_10 r1_node r2_node r2_sign)))
abbrev shared_expr_Repair018_26 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair018_8 r1_node r1_sign r2_node)) ∨ (shared_expr_Repair018_25 r1_depth r1_node r2_depth r2_node r2_sign))
theorem normalization_2558 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_617 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair018_26 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2546 r1_depth r2_depth) (normalization_2550 r1_node r1_sign r2_node)) (and_congr (not_congr (normalization_2546 r1_depth r2_depth)) (normalization_2557 r1_depth r1_node r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair018_27 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair018_6 r1_node r1_sign r2_node r2_sign)) ∨ ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair018_26 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
theorem normalization_2559 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_618 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair018_27 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2477 r1_depth r2_depth) (normalization_2545 r1_node r1_sign r2_node r2_sign)) (and_congr (not_congr (normalization_2477 r1_depth r2_depth)) (normalization_2558 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))

theorem normalization_2560 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((r2_kind = (2 : Int)) ∨ (formula_618 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ↔ ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair018_27 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) := (or_congr (normalization_201 r2_kind) (normalization_2559 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))

abbrev shared_expr_Repair018_28 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ∧ ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair018_27 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
theorem normalization_2561 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (r2_kind = (0 : Int))) ∧ (¬ (r1_kind = (2 : Int))) ∧ ((r2_kind = (2 : Int)) ∨ (formula_618 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))) ↔ (shared_expr_Repair018_28 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := (and_congr (normalization_2498 r2_kind) (and_congr (normalization_2512 r1_kind) (normalization_2560 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair018_29 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_4 r1_group r1_kind r1_level r1_mode r2_group r2_kind r2_level r2_mode) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair018_28 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_2562 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_619 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_29 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (or_congr (and_congr (normalization_2270 r1_kind) (normalization_2542 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) (and_congr (not_congr (normalization_2270 r1_kind)) (normalization_2561 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair018_30 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_15 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_29 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_2563 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_620 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_30 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_2530 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_2562 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_703 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_620 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_461 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (shared_expr_Repair018_6 r1_node r1_sign r2_node r2_sign) (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) (shared_expr_Repair018_8 r1_node r1_sign r2_node) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) (shared_expr_Repair018_10 r1_node r2_node r2_sign))
  have hn := ht
  exact Iff.mpr (normalization_2563 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

-- Checked replay of mp.
theorem replay_704 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (formula_619 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_703 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_702 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62)

theorem normalized_462 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2564 (r2_kind : Int) : (¬ (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))))) := (not_congr (normalization_369 r2_kind))

theorem normalization_2565 (r2_kind : Int) : ((¬ (r2_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))))) ↔ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))))))) := (iff_congr (normalization_2498 r2_kind) (normalization_2564 r2_kind))

-- Checked replay of monotonicity.
theorem replay_705 (r2_kind : Int) : ((¬ (r2_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_462 (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))))
  have n0 : ((((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_371 r2_kind) (replay_68 r2_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_2565 r2_kind) hn

theorem normalized_463 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2566 (r2_kind : Int) : ((¬ (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) ↔ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) ↔ ((¬ (¬ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_2564 r2_kind) (normalization_368 r2_kind))

-- Checked replay of rewrite.
theorem replay_706 (r2_kind : Int) : ((¬ (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) ↔ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_463 ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_2566 r2_kind) hn

theorem normalized_464 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2567 (r2_kind : Int) : ((¬ (r2_kind = (0 : Int))) ↔ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) ↔ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_2498 r2_kind) (normalization_368 r2_kind))

-- Checked replay of trans.
theorem replay_707 (r2_kind : Int) : ((¬ (r2_kind = (0 : Int))) ↔ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_464 (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))))
  have n0 : ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))))))) := by
    exact Iff.mp (normalization_2565 r2_kind) (replay_705 r2_kind)
  have n1 : ((¬ (¬ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_2566 r2_kind) (replay_706 r2_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2567 r2_kind) hn

abbrev shared_expr_Repair018_31 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_613 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))) ↔ ((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))))
abbrev formula_621 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair018_31 r1_group r1_level r1_mode r2_group r2_level r2_mode)

theorem normalized_465 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2568 (r1_level r2_level : Int) : ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ↔ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_2569 (r1_level r2_level : Int) : (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ↔ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (not_congr (normalization_2568 r1_level r2_level))

theorem normalization_2570 (r1_level r2_level : Int) : ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ↔ ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) := (or_congr (normalization_2569 r1_level r2_level) (normalization_2539 r1_level r2_level))

theorem normalization_2571 (r1_mode r2_mode : Int) : ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ↔ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_2572 (r1_mode r2_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ↔ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := (not_congr (normalization_2571 r1_mode r2_mode))

theorem normalization_2573 (r1_mode r2_mode : Int) : ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ↔ ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_2572 r1_mode r2_mode) (normalization_2536 r1_mode r2_mode))

abbrev shared_expr_Repair018_32 (r1_group r1_mode r2_group r2_mode : Int) : Prop := ((((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))))))
theorem normalization_2574 (r1_group r1_mode r2_group r2_mode : Int) : (formula_596 r1_group r1_mode r2_group r2_mode) ↔ (shared_expr_Repair018_32 r1_group r1_mode r2_group r2_mode) := (or_congr (and_congr (normalization_2573 r1_mode r2_mode) (normalization_2536 r1_mode r2_mode)) (and_congr (not_congr (normalization_2573 r1_mode r2_mode)) (normalization_2534 r1_group r2_group)))

abbrev shared_expr_Repair018_33 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair018_32 r1_group r1_mode r2_group r2_mode)))
theorem normalization_2575 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode) ↔ (shared_expr_Repair018_33 r1_group r1_level r1_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_2570 r1_level r2_level) (normalization_2539 r1_level r2_level)) (and_congr (not_congr (normalization_2570 r1_level r2_level)) (normalization_2574 r1_group r1_mode r2_group r2_mode)))

abbrev shared_expr_Repair018_34 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair018_33 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))))) ∧ (¬ ((r1_mode) ≤ (3 : Int)))))
theorem normalization_2576 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : ((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))) ↔ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_2499 r1_mode r2_mode) (normalization_2575 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_2499 r1_mode r2_mode)) (normalization_2271 r1_mode)))

theorem normalization_2577 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_621 r1_group r1_level r1_mode r2_group r2_level r2_mode) ↔ ((shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode) ↔ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)) := (iff_congr (normalization_2541 r1_group r1_level r1_mode r2_group r2_level r2_mode) (normalization_2576 r1_group r1_level r1_mode r2_group r2_level r2_mode))

-- Checked replay of rewrite.
theorem replay_708 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_621 r1_group r1_level r1_mode r2_group r2_level r2_mode) := by
  classical
  have ht := (normalized_465 ((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))) ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) ((r1_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2577 r1_group r1_level r1_mode r2_group r2_level r2_mode) hn

abbrev shared_expr_Repair018_35 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) ∨ ((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))))
abbrev formula_622 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (shared_expr_Repair018_35 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)

theorem normalized_466 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2578 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : (formula_622 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ (((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)) := (or_congr (normalization_368 r2_kind) (normalization_2576 r1_group r1_level r1_mode r2_group r2_level r2_mode))

abbrev shared_expr_Repair018_36 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ↔ (((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)))
theorem normalization_2579 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : ((formula_614 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ (formula_622 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) ↔ (shared_expr_Repair018_36 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) := (iff_congr (normalization_2542 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) (normalization_2578 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode))

-- Checked replay of monotonicity.
theorem replay_709 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : ((formula_614 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ (formula_622 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) := by
  classical
  have ht := (normalized_466 (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))) (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode) (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode))
  have n0 : ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_2567 r2_kind) (replay_707 r2_kind)
  have n1 : ((shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode) ↔ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)) := by
    exact Iff.mp (normalization_2577 r1_group r1_level r1_mode r2_group r2_level r2_mode) (replay_708 r1_group r1_level r1_mode r2_group r2_level r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2579 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) hn

theorem normalized_467 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2580 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : (formula_598 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)) := (or_congr (normalization_366 r2_kind) (or_congr (normalization_367 r2_kind) (normalization_2576 r1_group r1_level r1_mode r2_group r2_level r2_mode)))

abbrev shared_expr_Repair018_37 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ↔ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)))
theorem normalization_2581 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : ((formula_622 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ (formula_598 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) ↔ (shared_expr_Repair018_37 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) := (iff_congr (normalization_2578 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) (normalization_2580 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode))

-- Checked replay of rewrite.
theorem replay_710 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : ((formula_622 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ (formula_598 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) := by
  classical
  have ht := (normalized_467 ((r2_kind) ≤ (0 : Int)) ((r2_kind) ≤ (-1 : Int)) (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode))
  have hn := ht
  exact Iff.mpr (normalization_2581 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) hn

theorem normalized_468 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair018_38 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ↔ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)))
theorem normalization_2582 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : ((formula_614 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ (formula_598 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) ↔ (shared_expr_Repair018_38 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) := (iff_congr (normalization_2542 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) (normalization_2580 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode))

-- Checked replay of trans.
theorem replay_711 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : ((formula_614 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) ↔ (formula_598 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) := by
  classical
  have ht := (normalized_468 ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)))
  have n0 : (shared_expr_Repair018_36 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) := by
    exact Iff.mp (normalization_2579 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) (replay_709 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)
  have n1 : (shared_expr_Repair018_37 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) := by
    exact Iff.mp (normalization_2581 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) (replay_710 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2582 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) hn

theorem normalized_469 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2583 (r1_kind : Int) : ((r1_kind ≤ (2 : Int)) ∧ (r1_kind ≥ (2 : Int))) ↔ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) := (and_congr (normalization_2409 r1_kind) (normalization_2411 r1_kind))

theorem normalization_2584 (r1_kind : Int) : ((r1_kind = (2 : Int)) ↔ ((r1_kind ≤ (2 : Int)) ∧ (r1_kind ≥ (2 : Int)))) ↔ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ↔ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) := (iff_congr (normalization_2284 r1_kind) (normalization_2583 r1_kind))

-- Checked replay of rewrite.
theorem replay_712 (r1_kind : Int) : ((r1_kind = (2 : Int)) ↔ ((r1_kind ≤ (2 : Int)) ∧ (r1_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_469 (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2584 r1_kind) hn

theorem normalized_470 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2585 (r1_kind : Int) : (((r1_kind ≤ (2 : Int)) ∧ (r1_kind ≥ (2 : Int))) ↔ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ↔ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_2583 r1_kind) (normalization_2414 r1_kind))

-- Checked replay of rewrite.
theorem replay_713 (r1_kind : Int) : (((r1_kind ≤ (2 : Int)) ∧ (r1_kind ≥ (2 : Int))) ↔ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_470 ((r1_kind) ≤ (2 : Int)) ((r1_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2585 r1_kind) hn

theorem normalized_471 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2586 (r1_kind : Int) : ((r1_kind = (2 : Int)) ↔ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ↔ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_2284 r1_kind) (normalization_2414 r1_kind))

-- Checked replay of trans.
theorem replay_714 (r1_kind : Int) : ((r1_kind = (2 : Int)) ↔ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_471 (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))))
  have n0 : ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ↔ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_2584 r1_kind) (replay_712 r1_kind)
  have n1 : ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2585 r1_kind) (replay_713 r1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2586 r1_kind) hn

theorem normalized_472 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2587 (r1_kind : Int) : (¬ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ↔ (¬ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) := (not_congr (normalization_2414 r1_kind))

theorem normalization_2588 (r1_kind : Int) : ((¬ (r1_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))))) ↔ ((¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))))) := (iff_congr (normalization_2512 r1_kind) (normalization_2587 r1_kind))

-- Checked replay of monotonicity.
theorem replay_715 (r1_kind : Int) : ((¬ (r1_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_472 (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))
  have n0 : ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2586 r1_kind) (replay_714 r1_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_2588 r1_kind) hn

theorem normalized_473 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2589 (r1_kind : Int) : ((¬ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ↔ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ↔ ((¬ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) ↔ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_2587 r1_kind) (normalization_2413 r1_kind))

-- Checked replay of rewrite.
theorem replay_716 (r1_kind : Int) : ((¬ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ↔ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_473 ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_2589 r1_kind) hn

theorem normalized_474 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2590 (r1_kind : Int) : ((¬ (r1_kind = (2 : Int))) ↔ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ↔ ((¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ↔ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_2512 r1_kind) (normalization_2413 r1_kind))

-- Checked replay of trans.
theorem replay_717 (r1_kind : Int) : ((¬ (r1_kind = (2 : Int))) ↔ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_474 (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))
  have n0 : ((¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_2588 r1_kind) (replay_715 r1_kind)
  have n1 : ((¬ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) ↔ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_2589 r1_kind) (replay_716 r1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2590 r1_kind) hn

abbrev shared_expr_Repair018_39 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((r2_kind = (2 : Int)) ∨ (formula_618 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ↔ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (formula_561 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
abbrev formula_623 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_39 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign)

theorem normalized_475 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : (((p0 ∧ (¬ p1)) ∨ (((p2 ∧ (¬ p3)) ∧ (((p4 ∧ (¬ p5)) ∧ ((p6 ∧ (¬ p7)) ∧ (p8 ∧ (¬ p9)))) ∨ ((¬ (p4 ∧ (¬ p5))) ∧ (¬ (¬ p5))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p3 ∧ (¬ p10)) ∧ ((((¬ p11) ∧ p12) ∧ (p6 ∧ (¬ p7))) ∨ ((¬ ((¬ p11) ∧ p12)) ∧ (¬ p12)))) ∨ ((¬ (p3 ∧ (¬ p10))) ∧ ((¬ (p13 ∧ (¬ p2))) ∨ ((((¬ p14) ∧ p15) ∧ (p8 ∧ (¬ p9))) ∨ ((¬ ((¬ p14) ∧ p15)) ∧ (¬ (¬ p14)))))))))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ ((((¬ p2) ∨ (¬ (¬ p3))) ∧ ((((¬ p3) ∨ (¬ (¬ p10))) ∧ ((¬ p13) ∨ (¬ (¬ p2)) ∨ ((((¬ (¬ p14)) ∨ (¬ p15)) ∧ (¬ (¬ p14))) ∨ ((¬ ((¬ (¬ p14)) ∨ (¬ p15))) ∧ (¬ ((¬ p8) ∨ (¬ (¬ p9)))))))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p10)))) ∧ ((((¬ (¬ p11)) ∨ (¬ p12)) ∧ (¬ p12)) ∨ ((¬ ((¬ (¬ p11)) ∨ (¬ p12))) ∧ (¬ ((¬ p6) ∨ (¬ (¬ p7))))))))) ∨ ((¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ ((((¬ p4) ∨ (¬ (¬ p5))) ∧ (¬ (¬ p5))) ∨ ((¬ ((¬ p4) ∨ (¬ (¬ p5)))) ∧ (¬ ((¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ p8) ∨ (¬ (¬ p9)))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2591 (r1_depth r2_depth : Int) : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ↔ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2592 (r1_depth r2_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (not_congr (normalization_2591 r1_depth r2_depth))

theorem normalization_2593 (r1_depth r2_depth : Int) : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ↔ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2594 (r1_depth r2_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2593 r1_depth r2_depth))

theorem normalization_2595 (r1_depth r2_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))) ↔ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_2592 r1_depth r2_depth) (normalization_2594 r1_depth r2_depth))

theorem normalization_2596 (r1_depth r2_depth : Int) : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ↔ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2597 (r1_depth r2_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := (not_congr (normalization_2596 r1_depth r2_depth))

theorem normalization_2598 (r1_depth r2_depth : Int) : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int)) ↔ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_2599 (r1_depth r2_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_2598 r1_depth r2_depth))

theorem normalization_2600 (r1_depth r2_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_2597 r1_depth r2_depth) (normalization_2599 r1_depth r2_depth))

theorem normalization_2601 (r1_depth r2_depth : Int) : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ↔ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_2602 (r1_depth r2_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ↔ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) := (not_congr (normalization_2601 r1_depth r2_depth))

theorem normalization_2603 (r1_depth r2_depth : Int) : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int)) ↔ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_2604 (r1_depth r2_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := (not_congr (normalization_2603 r1_depth r2_depth))

theorem normalization_2605 (r1_node r2_node : Int) : ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2606 (r1_node r2_node : Int) : (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := (not_congr (normalization_2605 r1_node r2_node))

theorem normalization_2607 (r1_node r2_node : Int) : ((¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) := (or_congr (normalization_2555 r1_node r2_node) (normalization_2606 r1_node r2_node))

abbrev shared_expr_Repair018_40 (r1_node r2_node : Int) : Prop := (((¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair018_41 (r1_node r2_node r2_sign : Int) : Prop := ((¬ ((¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))))
theorem normalization_2608 (r1_node r2_node r2_sign : Int) : (formula_558 r1_node r2_node r2_sign) ↔ ((shared_expr_Repair018_40 r1_node r2_node) ∨ (shared_expr_Repair018_41 r1_node r2_node r2_sign)) := (or_congr (and_congr (normalization_2607 r1_node r2_node) (normalization_2555 r1_node r2_node)) (and_congr (not_congr (normalization_2607 r1_node r2_node)) (normalization_605 r2_sign)))

abbrev shared_expr_Repair018_42 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) ∨ ((shared_expr_Repair018_40 r1_node r2_node) ∨ (shared_expr_Repair018_41 r1_node r2_node r2_sign)))
theorem normalization_2609 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_558 r1_node r2_node r2_sign)) ↔ (shared_expr_Repair018_42 r1_depth r1_node r2_depth r2_node r2_sign) := (or_congr (normalization_2602 r1_depth r2_depth) (or_congr (normalization_2604 r1_depth r2_depth) (normalization_2608 r1_node r2_node r2_sign)))

theorem normalization_2610 (r1_node r2_node : Int) : ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2611 (r1_node r2_node : Int) : (¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2610 r1_node r2_node))

theorem normalization_2612 (r1_node r2_node : Int) : ((¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) := (or_congr (normalization_2611 r1_node r2_node) (normalization_2549 r1_node r2_node))

theorem normalization_2613 (r1_sign : Int) : (r1_sign ≤ (1 : Int)) ↔ ((r1_sign) ≤ (1 : Int)) := by
  omega

theorem normalization_2614 (r1_sign : Int) : (¬ (r1_sign ≤ (1 : Int))) ↔ (¬ ((r1_sign) ≤ (1 : Int))) := (not_congr (normalization_2613 r1_sign))

theorem normalization_2615 (r1_sign : Int) : (r1_sign ≥ (1 : Int)) ↔ (¬ ((r1_sign) ≤ (0 : Int))) := by
  omega

theorem normalization_2616 (r1_sign : Int) : (¬ (r1_sign ≥ (1 : Int))) ↔ (¬ (¬ ((r1_sign) ≤ (0 : Int)))) := (not_congr (normalization_2615 r1_sign))

theorem normalization_2617 (r1_sign : Int) : ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))) ↔ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))) := (or_congr (normalization_2614 r1_sign) (normalization_2616 r1_sign))

theorem normalization_2618 (r1_sign : Int) : (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) := (not_congr (normalization_2617 r1_sign))

abbrev shared_expr_Repair018_43 (r1_node r2_node : Int) : Prop := (((¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) ∧ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair018_44 (r1_node r1_sign r2_node : Int) : Prop := ((¬ ((¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))))
theorem normalization_2619 (r1_node r1_sign r2_node : Int) : (formula_559 r1_node r1_sign r2_node) ↔ ((shared_expr_Repair018_43 r1_node r2_node) ∨ (shared_expr_Repair018_44 r1_node r1_sign r2_node)) := (or_congr (and_congr (normalization_2612 r1_node r2_node) (normalization_2549 r1_node r2_node)) (and_congr (not_congr (normalization_2612 r1_node r2_node)) (normalization_2618 r1_sign)))

abbrev shared_expr_Repair018_45 (r1_depth r1_node r1_sign r2_depth r2_node : Int) : Prop := ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))))) ∧ ((shared_expr_Repair018_43 r1_node r2_node) ∨ (shared_expr_Repair018_44 r1_node r1_sign r2_node)))
abbrev shared_expr_Repair018_46 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair018_42 r1_depth r1_node r2_depth r2_node r2_sign)) ∨ (shared_expr_Repair018_45 r1_depth r1_node r1_sign r2_depth r2_node))
theorem normalization_2620 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_560 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair018_46 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2600 r1_depth r2_depth) (normalization_2609 r1_depth r1_node r2_depth r2_node r2_sign)) (and_congr (not_congr (normalization_2600 r1_depth r2_depth)) (normalization_2619 r1_node r1_sign r2_node)))

theorem normalization_2621 (r1_node r2_node : Int) : ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ↔ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2622 (r1_node r2_node : Int) : (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ↔ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := (not_congr (normalization_2621 r1_node r2_node))

theorem normalization_2623 (r1_node r2_node : Int) : ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) ↔ ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) := (or_congr (normalization_2622 r1_node r2_node) (normalization_2544 r1_node r2_node))

theorem normalization_2624 (r1_sign r2_sign : Int) : ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))) ↔ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))) := (or_congr (normalization_2614 r1_sign) (or_congr (normalization_2616 r1_sign) (or_congr (normalization_576 r2_sign) (normalization_578 r2_sign))))

theorem normalization_2625 (r1_sign r2_sign : Int) : (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ↔ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) := (not_congr (normalization_2624 r1_sign r2_sign))

abbrev shared_expr_Repair018_47 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Repair018_48 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_47 r1_node r1_sign r2_node r2_sign))
theorem normalization_2626 (r1_node r1_sign r2_node r2_sign : Int) : (formula_556 r1_node r1_sign r2_node r2_sign) ↔ (shared_expr_Repair018_48 r1_node r1_sign r2_node r2_sign) := (or_congr (and_congr (normalization_2623 r1_node r2_node) (normalization_2544 r1_node r2_node)) (and_congr (not_congr (normalization_2623 r1_node r2_node)) (normalization_2625 r1_sign r2_sign)))

abbrev shared_expr_Repair018_49 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair018_46 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ∨ ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair018_48 r1_node r1_sign r2_node r2_sign)))
theorem normalization_2627 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_561 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair018_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2595 r1_depth r2_depth) (normalization_2620 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) (and_congr (not_congr (normalization_2595 r1_depth r2_depth)) (normalization_2626 r1_node r1_sign r2_node r2_sign)))

theorem normalization_2628 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (formula_561 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ↔ ((¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair018_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) := (or_congr (normalization_564 r2_kind) (normalization_2627 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))

abbrev shared_expr_Repair018_50 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair018_27 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ↔ ((¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair018_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
theorem normalization_2629 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_623 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Repair018_50 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := (iff_congr (normalization_2560 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (normalization_2628 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_718 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_623 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := by
  classical
  have ht := (normalized_475 ((r2_kind) ≤ (2 : Int)) ((r2_kind) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) ((r1_sign) ≤ (1 : Int)) ((r1_sign) ≤ (0 : Int)) ((r2_sign) ≤ (0 : Int)) ((r2_sign) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2629 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign) hn

abbrev shared_expr_Repair018_51 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) ∧ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))) ∧ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (formula_561 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
abbrev formula_624 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_51 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair018_52 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((¬ (r2_kind = (0 : Int))) ∧ (¬ (r1_kind = (2 : Int))) ∧ ((r2_kind = (2 : Int)) ∨ (formula_618 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))) ↔ (formula_624 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))
abbrev formula_625 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_52 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)

theorem normalized_476 (p0 p1 p2 p3 p4 p5 : Prop) : ((((¬ p0) ↔ p1) ∧ ((¬ p2) ↔ p3) ∧ (p4 ↔ p5)) → (((¬ p0) ∧ (¬ p2) ∧ p4) ↔ (p1 ∧ p3 ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair018_53 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))) ∧ ((¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair018_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
theorem normalization_2630 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_624 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Repair018_53 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := (and_congr (normalization_368 r2_kind) (and_congr (normalization_2413 r1_kind) (normalization_2628 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

theorem normalization_2631 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_625 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ ((shared_expr_Repair018_28 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Repair018_53 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)) := (iff_congr (normalization_2561 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (normalization_2630 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_719 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_625 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := by
  classical
  have ht := (normalized_476 (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))) (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))) ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair018_27 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ((¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair018_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
  have n0 : ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_2567 r2_kind) (replay_707 r2_kind)
  have n1 : ((¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ↔ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_2590 r1_kind) (replay_717 r1_kind)
  have n2 : (shared_expr_Repair018_50 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := by
    exact Iff.mp (normalization_2629 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (replay_718 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2631 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) hn

theorem normalized_477 (p0 p1 p2 : Prop) : ((p0 ∧ p1 ∧ p2) ↔ (¬ ((¬ p1) ∨ (¬ p0) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2632 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (¬ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (formula_561 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))) ↔ (¬ ((¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair018_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))) := (not_congr (normalization_2628 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign))

abbrev shared_expr_Repair018_54 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair018_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))))
theorem normalization_2633 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := (or_congr (normalization_2414 r1_kind) (or_congr (normalization_369 r2_kind) (normalization_2632 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

theorem normalization_2634 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)) ↔ (¬ (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)) := (not_congr (normalization_2633 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))

theorem normalization_2635 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((formula_624 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) ↔ ((shared_expr_Repair018_53 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (¬ (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) := (iff_congr (normalization_2630 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (normalization_2634 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_720 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((formula_624 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) := by
  classical
  have ht := (normalized_477 ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int))))) ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))) ((¬ ((¬ ((r2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair018_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
  have hn := ht
  exact Iff.mpr (normalization_2635 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) hn

abbrev shared_expr_Repair018_55 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((¬ (r2_kind = (0 : Int))) ∧ (¬ (r1_kind = (2 : Int))) ∧ ((r2_kind = (2 : Int)) ∨ (formula_618 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))) ↔ (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))
abbrev formula_626 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_55 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)

theorem normalized_478 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2636 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_626 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ ((shared_expr_Repair018_28 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (¬ (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) := (iff_congr (normalization_2561 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (normalization_2634 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))

-- Checked replay of trans.
theorem replay_721 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_626 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := by
  classical
  have ht := (normalized_478 (shared_expr_Repair018_28 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (shared_expr_Repair018_53 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))
  have n0 : ((shared_expr_Repair018_28 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Repair018_53 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)) := by
    exact Iff.mp (normalization_2631 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (replay_719 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)
  have n1 : ((shared_expr_Repair018_53 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (¬ (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) := by
    exact Iff.mp (normalization_2635 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (replay_720 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2636 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) hn

abbrev shared_expr_Repair018_56 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ∧ (formula_598 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) ∨ ((¬ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) ∧ (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))))
abbrev formula_627 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_56 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Repair018_57 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_619 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_627 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_628 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_57 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_479 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair018_58 (r1_group r1_kind r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) ∧ ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)))
abbrev shared_expr_Repair018_59 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_58 r1_group r1_kind r1_level r1_mode r2_group r2_kind r2_level r2_mode) ∨ ((¬ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) ∧ (¬ (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))))
theorem normalization_2637 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_627 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_59 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (or_congr (and_congr (normalization_2379 r1_kind) (normalization_2580 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) (and_congr (not_congr (normalization_2379 r1_kind)) (normalization_2634 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair018_60 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_29 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_59 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_2638 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_628 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_60 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_2562 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_2637 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_722 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_628 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_479 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair018_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (shared_expr_Repair018_28 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))
  have n0 : ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_2381 r1_kind) (replay_509 r1_kind)
  have n1 : (shared_expr_Repair018_38 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) := by
    exact Iff.mp (normalization_2582 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) (replay_711 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)
  have n2 : ((shared_expr_Repair018_28 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (¬ (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) := by
    exact Iff.mp (normalization_2636 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (replay_721 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2638 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

abbrev shared_expr_Repair018_61 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_627 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_599 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_629 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_61 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_480 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair018_62 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (¬ (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) ∨ (shared_expr_Repair018_58 r1_group r1_kind r1_level r1_mode r2_group r2_kind r2_level r2_mode))
theorem normalization_2639 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_599 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_62 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (or_congr (and_congr (normalization_2378 r1_kind) (normalization_2634 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)) (and_congr (not_congr (normalization_2378 r1_kind)) (normalization_2580 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)))

abbrev shared_expr_Repair018_63 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_59 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_62 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_2640 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_629 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_63 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_2637 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_2639 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_723 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_629 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_480 ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ((¬ ((r2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair018_34 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (shared_expr_Repair018_54 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))
  have hn := ht
  exact Iff.mpr (normalization_2640 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

abbrev shared_expr_Repair018_64 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_619 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_599 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_630 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair018_64 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_481 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair018_65 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair018_29 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_62 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_2641 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_630 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair018_65 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_2562 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_2639 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of trans.
theorem replay_724 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_630 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_481 (shared_expr_Repair018_29 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (shared_expr_Repair018_59 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (shared_expr_Repair018_62 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
  have n0 : (shared_expr_Repair018_60 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
    exact Iff.mp (normalization_2638 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_722 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)
  have n1 : (shared_expr_Repair018_63 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
    exact Iff.mp (normalization_2640 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_723 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2641 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

-- Checked replay of mp.
theorem replay_725 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (formula_599 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact Iff.mp (replay_724 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (replay_704 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62)

-- Checked replay of unit-resolution.
theorem replay_726 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : ((¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ∨ (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_698 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (Or.inl l0)) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_725 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62)))))))

theorem propositional_482 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_727 (r1_kind : Int) : (((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) ∨ (r1_kind ≤ (0 : Int))) := by
  exact (propositional_482 (r1_kind ≤ (0 : Int)) (r1_kind ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_728 (r1_kind : Int) : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_729 (r1_kind : Int) (i41 : (r1_kind ≥ (1 : Int))) : (¬ (r1_kind ≤ (0 : Int))) := by
  exact (Or.elim (replay_728 r1_kind) (fun l0 => l0) (fun t0 => (False.elim (t0 i41))))

-- Checked replay of unit-resolution.
theorem replay_730 (r1_kind : Int) (i41 : (r1_kind ≥ (1 : Int))) : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) := by
  exact (Or.elim (replay_727 r1_kind) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_729 r1_kind i41) t0))))

-- Checked replay of unit-resolution.
theorem replay_731 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i41 : (r1_kind ≥ (1 : Int))) : (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_726 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62) (fun l0 => (False.elim (l0 (replay_730 r1_kind i41)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_732 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i41 : (r1_kind ≥ (1 : Int))) : ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) := by
  exact (Or.elim (replay_697 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim ((replay_731 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62 i41) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_733 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i41 : (r1_kind ≥ (1 : Int))) : (¬ (r2_kind ≤ (0 : Int))) := by
  exact (Or.elim (replay_138 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10) (fun l0 => (False.elim (l0 (replay_732 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62 i41)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_734 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i41 : (r1_kind ≥ (1 : Int))) : (formula_36 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (Or.elim (replay_139 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_733 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10 i62 i41) t0))))

-- Checked replay of unit-resolution.
theorem replay_735 (c0_group c0_level c0_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i41 : (r1_kind ≥ (1 : Int))) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_171 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) := by
  exact (Or.elim (replay_126 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10) (fun l0 => (False.elim (l0 (replay_696 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i50 i51 i52)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_734 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10 i62 i41)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_736 (c0_group c0_level c0_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i41 : (r1_kind ≥ (1 : Int))) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (formula_170 h r2_depth r2_sign) := by
  exact (Or.elim (replay_692 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (False.elim ((replay_735 c0_group c0_level c0_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10 i62 i41 i50 i51 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_737 (c0_group c0_level c0_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i41 : (r1_kind ≥ (1 : Int))) (i63 : ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))) := by
  exact (Or.elim (replay_691 h r2_depth r2_sign) (fun l0 => (False.elim (l0 (replay_736 c0_group c0_level c0_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10 i62 i41 i50 i51 i52)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i63))) (fun t1 => (Or.elim t1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))))

theorem propositional_483 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_738 (r2_sign : Int) : (((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))) ∨ (r2_sign ≤ (0 : Int))) := by
  exact (propositional_483 (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_739 (r2_sign : Int) : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair018_66 (r2_sign : Int) : Prop := ((¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))
abbrev formula_631 (r2_sign : Int) : Prop := (shared_expr_Repair018_66 r2_sign)

theorem propositional_484 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_740 (r2_sign : Int) : (formula_631 r2_sign) := by
  exact (propositional_484 ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))) ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))

theorem propositional_485 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_741 (r2_sign : Int) : (((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))) ∨ (r2_sign ≥ (1 : Int))) := by
  exact (propositional_485 (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_742 (r2_sign : Int) (i64 : (¬ (r2_sign ≥ (1 : Int)))) : ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))) := by
  exact (Or.elim (replay_741 r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i64 t0))))

-- Checked replay of unit-resolution.
theorem replay_743 (r2_sign : Int) (i64 : (¬ (r2_sign ≥ (1 : Int)))) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_740 r2_sign) (fun l0 => (False.elim (l0 i65))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_742 r2_sign i64)))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_744 (r2_sign : Int) : ((r2_sign ≥ (1 : Int)) ∨ (¬ (r2_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_745 (r2_sign : Int) (i64 : (¬ (r2_sign ≥ (1 : Int)))) : (¬ (r2_sign ≥ (2 : Int))) := by
  exact (Or.elim (replay_744 r2_sign) (fun l0 => (False.elim (i64 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_746 (r2_sign : Int) (i64 : (¬ (r2_sign ≥ (1 : Int)))) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : False := by
  exact (Or.elim (replay_685 r2_sign) (fun l0 => (False.elim ((replay_743 r2_sign i64 i65) l0))) (fun t0 => (False.elim ((replay_745 r2_sign i64) t0))))

-- Checked replay of lemma.
theorem replay_747 (r2_sign : Int) : ((r2_sign ≥ (1 : Int)) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_746 r2_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr q))))

theorem propositional_486 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p4) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_748 (c0_level r2_depth r2_kind r2_sign : Int) : ((formula_67 c0_level r2_depth r2_kind r2_sign) ∨ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) := by
  exact (propositional_486 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))))

-- Checked replay of unit-resolution.
theorem replay_749 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) := by
  exact (Or.elim (replay_748 c0_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_676 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_750 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (r2_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_747 r2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_749 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52)))))

-- Checked replay of unit-resolution.
theorem replay_751 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (r2_sign ≤ (0 : Int))) := by
  exact (Or.elim (replay_739 r2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_750 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52)))))

end H4Formal.Generated.Repair
