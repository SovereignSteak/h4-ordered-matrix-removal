import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair014

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_502 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_535 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_501 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) i33

abbrev shared_expr_Repair015_0 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_535 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_535 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_537 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_0 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_368 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair015_1 (r0_group r0_mode r1_group r1_mode : Int) : Prop := (((((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))))) ∨ ((¬ (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair015_2 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (((((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair015_1 r0_group r0_mode r1_group r1_mode)) ∨ ((¬ (((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair015_3 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := ((((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair015_2 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int))))) ∧ (¬ ((r0_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair015_4 (r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode)))
abbrev shared_expr_Repair015_5 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∧ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))))
abbrev shared_expr_Repair015_6 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_5 r0_node r0_sign r1_node r1_sign) ∨ ((¬ (((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair015_7 (r0_node r1_node : Int) : Prop := ((¬ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)))) ∧ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair015_8 (r0_node r0_sign r1_node : Int) : Prop := ((((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) ∧ (((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair015_7 r0_node r1_node))
abbrev shared_expr_Repair015_9 (r0_node r1_node : Int) : Prop := ((¬ ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair015_10 (r0_node r1_node r1_sign : Int) : Prop := ((((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_9 r0_node r1_node))
abbrev shared_expr_Repair015_11 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair015_10 r0_node r1_node r1_sign)))
abbrev shared_expr_Repair015_12 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair015_8 r0_node r0_sign r1_node)) ∨ (shared_expr_Repair015_11 r0_depth r0_node r1_depth r1_node r1_sign))
abbrev shared_expr_Repair015_13 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair015_6 r0_node r0_sign r1_node r1_sign)) ∨ ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair015_12 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
abbrev shared_expr_Repair015_14 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ∧ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair015_13 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
abbrev shared_expr_Repair015_15 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_4 r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode) ∨ ((¬ (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair015_14 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Repair015_16 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_15 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_15 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2340 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_537 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_16 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_2338 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2338 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_503 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_537 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_368 (shared_expr_Repair015_15 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_2340 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_504 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_535 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_503 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_502 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33)

abbrev shared_expr_Repair015_17 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (((r0_level = r1_level) ∧ (((r0_mode = r1_mode) ∧ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int)))) ∨ ((¬ (r0_mode = r1_mode)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)))))) ∨ ((¬ (r0_level = r1_level)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)))))
abbrev formula_538 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair015_17 r0_group r0_level r0_mode r1_group r1_level r1_mode)

abbrev shared_expr_Repair015_18 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := ((¬ (r1_kind = (0 : Int))) ∨ ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_538 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))))
abbrev formula_539 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := (shared_expr_Repair015_18 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)

abbrev shared_expr_Repair015_19 (r0_node r0_sign r1_node : Int) : Prop := ((((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) = (0 : Int)) ∧ (r0_sign = (1 : Int))) ∨ ((¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))))
abbrev formula_540 (r0_node r0_sign r1_node : Int) : Prop := (shared_expr_Repair015_19 r0_node r0_sign r1_node)

abbrev shared_expr_Repair015_20 (r0_node r1_node r1_sign : Int) : Prop := ((((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) = (0 : Int)) ∧ (r1_sign = (0 : Int))) ∨ ((¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_541 (r0_node r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_20 r0_node r1_node r1_sign)

abbrev shared_expr_Repair015_21 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := ((((r0_depth + ((-1 : Int) * r1_depth)) = (-1 : Int)) ∧ (formula_540 r0_node r0_sign r1_node)) ∨ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) = (-1 : Int))) ∧ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) = (1 : Int))) ∨ (formula_541 r0_node r1_node r1_sign))))
abbrev formula_542 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_21 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)

abbrev shared_expr_Repair015_22 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((r0_depth = r1_depth) ∧ (((r0_node = r1_node) ∧ ((r0_sign = (1 : Int)) ∧ (r1_sign = (0 : Int)))) ∨ ((¬ (r0_node = r1_node)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int)))))) ∨ ((¬ (r0_depth = r1_depth)) ∧ (formula_542 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
abbrev formula_543 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_22 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)

abbrev shared_expr_Repair015_23 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((r0_kind = (0 : Int)) ∧ (formula_539 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) ∨ ((¬ (r0_kind = (0 : Int))) ∧ ((¬ (r1_kind = (0 : Int))) ∧ (¬ (r0_kind = (2 : Int))) ∧ ((r1_kind = (2 : Int)) ∨ (formula_543 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))))
abbrev formula_544 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_23 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair015_24 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_535 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_544 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_545 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_24 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_369 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ (¬ p3) ∧ (p4 ∨ ((p5 ∧ p6) ∨ ((¬ p5) ∧ ((p7 ∧ p8) ∨ ((¬ p7) ∧ ((¬ ((¬ p9) ∧ p10)) ∨ p11))))))))) ↔ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ (¬ p3) ∧ (p4 ∨ ((p5 ∧ p6) ∨ ((¬ p5) ∧ ((p7 ∧ p8) ∨ ((¬ p7) ∧ ((¬ (p10 ∧ (¬ p9))) ∨ p11)))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2341 (r0_group r1_group : Int) : ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int)) ↔ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2342 (r0_group r1_group : Int) : (¬ ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int))) ↔ (¬ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_2341 r0_group r1_group))

theorem normalization_2343 (r0_mode r1_mode : Int) : ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)) ↔ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2344 (r0_mode r1_mode : Int) : (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int))) ↔ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_2343 r0_mode r1_mode))

theorem normalization_2345 (r0_group r0_mode r1_group r1_mode : Int) : (((r0_mode = r1_mode) ∧ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int)))) ∨ ((¬ (r0_mode = r1_mode)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int))))) ↔ (shared_expr_Repair015_1 r0_group r0_mode r1_group r1_mode) := (or_congr (and_congr (normalization_2309 r0_mode r1_mode) (normalization_2342 r0_group r1_group)) (and_congr (not_congr (normalization_2309 r0_mode r1_mode)) (normalization_2344 r0_mode r1_mode)))

theorem normalization_2346 (r0_level r1_level : Int) : ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)) ↔ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2347 (r0_level r1_level : Int) : (¬ ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_2346 r0_level r1_level))

theorem normalization_2348 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : (formula_538 r0_group r0_level r0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair015_2 r0_group r0_level r0_mode r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_2308 r0_level r1_level) (normalization_2345 r0_group r0_mode r1_group r1_mode)) (and_congr (not_congr (normalization_2308 r0_level r1_level)) (normalization_2347 r0_level r1_level)))

theorem normalization_2349 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_538 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))) ↔ (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_2307 r0_mode r1_mode) (normalization_2348 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_2307 r0_mode r1_mode)) (normalization_1963 r0_mode)))

theorem normalization_2350 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : (formula_539 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode)) := (or_congr (normalization_2306 r1_kind) (normalization_2349 r0_group r0_level r0_mode r1_group r1_level r1_mode))

theorem normalization_2351 (r0_node r1_node : Int) : ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int)) ↔ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2352 (r0_node r1_node : Int) : (¬ ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int))) ↔ (¬ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2351 r0_node r1_node))

theorem normalization_2353 (r0_node r0_sign r1_node r1_sign : Int) : (((r0_node = r1_node) ∧ ((r0_sign = (1 : Int)) ∧ (r1_sign = (0 : Int)))) ∨ ((¬ (r0_node = r1_node)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int))))) ↔ (shared_expr_Repair015_6 r0_node r0_sign r1_node r1_sign) := (or_congr (and_congr (normalization_2286 r0_node r1_node) (normalization_2288 r0_sign r1_sign)) (and_congr (not_congr (normalization_2286 r0_node r1_node)) (normalization_2352 r0_node r1_node)))

theorem normalization_2354 (r0_depth r1_depth : Int) : ((r0_depth + ((-1 : Int) * r1_depth)) = (-1 : Int)) ↔ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_2355 (r0_node r1_node : Int) : ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2356 (r0_node r1_node : Int) : ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2357 (r0_node r1_node : Int) : (¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) := (not_congr (normalization_2356 r0_node r1_node))

theorem normalization_2358 (r0_node r0_sign r1_node : Int) : (formula_540 r0_node r0_sign r1_node) ↔ (shared_expr_Repair015_8 r0_node r0_sign r1_node) := (or_congr (and_congr (normalization_2355 r0_node r1_node) (normalization_1497 r0_sign)) (and_congr (not_congr (normalization_2355 r0_node r1_node)) (normalization_2357 r0_node r1_node)))

theorem normalization_2359 (r0_depth r1_depth : Int) : ((r0_depth + ((-1 : Int) * r1_depth)) = (1 : Int)) ↔ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := by
  omega

theorem normalization_2360 (r0_depth r1_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * r1_depth)) = (1 : Int))) ↔ (¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))) := (not_congr (normalization_2359 r0_depth r1_depth))

theorem normalization_2361 (r0_node r1_node : Int) : ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2362 (r0_node r1_node : Int) : ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2363 (r0_node r1_node : Int) : (¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2362 r0_node r1_node))

theorem normalization_2364 (r0_node r1_node r1_sign : Int) : (formula_541 r0_node r1_node r1_sign) ↔ (shared_expr_Repair015_10 r0_node r1_node r1_sign) := (or_congr (and_congr (normalization_2361 r0_node r1_node) (normalization_2287 r1_sign)) (and_congr (not_congr (normalization_2361 r0_node r1_node)) (normalization_2363 r0_node r1_node)))

theorem normalization_2365 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) = (1 : Int))) ∨ (formula_541 r0_node r1_node r1_sign)) ↔ ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair015_10 r0_node r1_node r1_sign)) := (or_congr (normalization_2360 r0_depth r1_depth) (normalization_2364 r0_node r1_node r1_sign))

abbrev shared_expr_Repair015_25 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair015_10 r0_node r1_node r1_sign)))
abbrev shared_expr_Repair015_26 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair015_8 r0_node r0_sign r1_node)) ∨ (shared_expr_Repair015_25 r0_depth r0_node r1_depth r1_node r1_sign))
theorem normalization_2366 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : (formula_542 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Repair015_26 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2354 r0_depth r1_depth) (normalization_2358 r0_node r0_sign r1_node)) (and_congr (not_congr (normalization_2354 r0_depth r1_depth)) (normalization_2365 r0_depth r0_node r1_depth r1_node r1_sign)))

abbrev shared_expr_Repair015_27 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair015_6 r0_node r0_sign r1_node r1_sign)) ∨ ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair015_26 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
theorem normalization_2367 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : (formula_543 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Repair015_27 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2285 r0_depth r1_depth) (normalization_2353 r0_node r0_sign r1_node r1_sign)) (and_congr (not_congr (normalization_2285 r0_depth r1_depth)) (normalization_2366 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))

theorem normalization_2368 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : ((r1_kind = (2 : Int)) ∨ (formula_543 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) ↔ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair015_27 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) := (or_congr (normalization_2284 r1_kind) (normalization_2367 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))

abbrev shared_expr_Repair015_28 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ∧ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair015_27 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
theorem normalization_2369 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (r1_kind = (0 : Int))) ∧ (¬ (r0_kind = (2 : Int))) ∧ ((r1_kind = (2 : Int)) ∨ (formula_543 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))) ↔ (shared_expr_Repair015_28 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := (and_congr (normalization_2306 r1_kind) (and_congr (normalization_2320 r0_kind) (normalization_2368 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair015_29 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_4 r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode) ∨ ((¬ (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair015_28 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))
theorem normalization_2370 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_544 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_29 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (and_congr (normalization_1438 r0_kind) (normalization_2350 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) (and_congr (not_congr (normalization_1438 r0_kind)) (normalization_2369 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair015_30 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_15 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_29 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2371 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_545 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_30 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_2338 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2370 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_505 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_545 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_369 (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) (shared_expr_Repair015_6 r0_node r0_sign r1_node r1_sign) (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) (shared_expr_Repair015_8 r0_node r0_sign r1_node) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) (shared_expr_Repair015_10 r0_node r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_2371 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_506 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_544 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_505 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_504 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33)

theorem normalized_370 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2372 (r1_kind : Int) : (r1_kind ≤ (0 : Int)) ↔ ((r1_kind) ≤ (0 : Int)) := by
  omega

theorem normalization_2373 (r1_kind : Int) : (r1_kind ≥ (0 : Int)) ↔ (¬ ((r1_kind) ≤ (-1 : Int))) := by
  omega

theorem normalization_2374 (r1_kind : Int) : ((r1_kind ≤ (0 : Int)) ∧ (r1_kind ≥ (0 : Int))) ↔ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) := (and_congr (normalization_2372 r1_kind) (normalization_2373 r1_kind))

theorem normalization_2375 (r1_kind : Int) : ((r1_kind = (0 : Int)) ↔ ((r1_kind ≤ (0 : Int)) ∧ (r1_kind ≥ (0 : Int)))) ↔ ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) := (iff_congr (normalization_2270 r1_kind) (normalization_2374 r1_kind))

-- Checked replay of rewrite.
theorem replay_507 (r1_kind : Int) : ((r1_kind = (0 : Int)) ↔ ((r1_kind ≤ (0 : Int)) ∧ (r1_kind ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_370 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2375 r1_kind) hn

theorem normalized_371 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2376 (r1_kind : Int) : (¬ (r1_kind ≤ (0 : Int))) ↔ (¬ ((r1_kind) ≤ (0 : Int))) := (not_congr (normalization_2372 r1_kind))

theorem normalization_2377 (r1_kind : Int) : (¬ (r1_kind ≥ (0 : Int))) ↔ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) := (not_congr (normalization_2373 r1_kind))

theorem normalization_2378 (r1_kind : Int) : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) := (or_congr (normalization_2376 r1_kind) (normalization_2377 r1_kind))

theorem normalization_2379 (r1_kind : Int) : (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ↔ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) := (not_congr (normalization_2378 r1_kind))

theorem normalization_2380 (r1_kind : Int) : (((r1_kind ≤ (0 : Int)) ∧ (r1_kind ≥ (0 : Int))) ↔ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) ↔ ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) := (iff_congr (normalization_2374 r1_kind) (normalization_2379 r1_kind))

-- Checked replay of rewrite.
theorem replay_508 (r1_kind : Int) : (((r1_kind ≤ (0 : Int)) ∧ (r1_kind ≥ (0 : Int))) ↔ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_371 ((r1_kind) ≤ (0 : Int)) ((r1_kind) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2380 r1_kind) hn

theorem normalized_372 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2381 (r1_kind : Int) : ((r1_kind = (0 : Int)) ↔ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) ↔ ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) := (iff_congr (normalization_2270 r1_kind) (normalization_2379 r1_kind))

-- Checked replay of trans.
theorem replay_509 (r1_kind : Int) : ((r1_kind = (0 : Int)) ↔ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_372 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))))
  have n0 : ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_2375 r1_kind) (replay_507 r1_kind)
  have n1 : ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_2380 r1_kind) (replay_508 r1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2381 r1_kind) hn

theorem normalized_373 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2382 (r1_kind : Int) : (¬ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) := (not_congr (normalization_2379 r1_kind))

theorem normalization_2383 (r1_kind : Int) : ((¬ (r1_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))))) ↔ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))))) := (iff_congr (normalization_2306 r1_kind) (normalization_2382 r1_kind))

-- Checked replay of monotonicity.
theorem replay_510 (r1_kind : Int) : ((¬ (r1_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_373 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))
  have n0 : ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_2381 r1_kind) (replay_509 r1_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_2383 r1_kind) hn

theorem normalized_374 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2384 (r1_kind : Int) : ((¬ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) ↔ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ↔ ((¬ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_2382 r1_kind) (normalization_2378 r1_kind))

-- Checked replay of rewrite.
theorem replay_511 (r1_kind : Int) : ((¬ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) ↔ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_374 ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_2384 r1_kind) hn

theorem normalized_375 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2385 (r1_kind : Int) : ((¬ (r1_kind = (0 : Int))) ↔ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ↔ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_2306 r1_kind) (normalization_2378 r1_kind))

-- Checked replay of trans.
theorem replay_512 (r1_kind : Int) : ((¬ (r1_kind = (0 : Int))) ↔ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_375 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))
  have n0 : ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))))) := by
    exact Iff.mp (normalization_2383 r1_kind) (replay_510 r1_kind)
  have n1 : ((¬ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_2384 r1_kind) (replay_511 r1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2385 r1_kind) hn

abbrev shared_expr_Repair015_31 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_538 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))) ↔ ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))))
abbrev formula_546 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair015_31 r0_group r0_level r0_mode r1_group r1_level r1_mode)

theorem normalized_376 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2386 (r0_level r1_level : Int) : ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_2387 (r0_level r1_level : Int) : (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_2386 r0_level r1_level))

theorem normalization_2388 (r0_level r1_level : Int) : ((¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)))) ↔ ((¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) := (or_congr (normalization_2387 r0_level r1_level) (normalization_2347 r0_level r1_level))

theorem normalization_2389 (r0_mode r1_mode : Int) : ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_2390 (r0_mode r1_mode : Int) : (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (not_congr (normalization_2389 r0_mode r1_mode))

theorem normalization_2391 (r0_mode r1_mode : Int) : ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)))) ↔ ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_2390 r0_mode r1_mode) (normalization_2344 r0_mode r1_mode))

abbrev shared_expr_Repair015_32 (r0_group r0_mode r1_group r1_mode : Int) : Prop := ((((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))))))
theorem normalization_2392 (r0_group r0_mode r1_group r1_mode : Int) : (formula_521 r0_group r0_mode r1_group r1_mode) ↔ (shared_expr_Repair015_32 r0_group r0_mode r1_group r1_mode) := (or_congr (and_congr (normalization_2391 r0_mode r1_mode) (normalization_2344 r0_mode r1_mode)) (and_congr (not_congr (normalization_2391 r0_mode r1_mode)) (normalization_2342 r0_group r1_group)))

abbrev shared_expr_Repair015_33 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := ((((¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair015_32 r0_group r0_mode r1_group r1_mode)))
theorem normalization_2393 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair015_33 r0_group r0_level r0_mode r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_2388 r0_level r1_level) (normalization_2347 r0_level r1_level)) (and_congr (not_congr (normalization_2388 r0_level r1_level)) (normalization_2392 r0_group r0_mode r1_group r1_mode)))

abbrev shared_expr_Repair015_34 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := ((((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair015_33 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int))))) ∧ (¬ ((r0_mode) ≤ (3 : Int)))))
theorem normalization_2394 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))) ↔ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_2307 r0_mode r1_mode) (normalization_2393 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_2307 r0_mode r1_mode)) (normalization_1963 r0_mode)))

theorem normalization_2395 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : (formula_546 r0_group r0_level r0_mode r1_group r1_level r1_mode) ↔ ((shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)) := (iff_congr (normalization_2349 r0_group r0_level r0_mode r1_group r1_level r1_mode) (normalization_2394 r0_group r0_level r0_mode r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_513 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : (formula_546 r0_group r0_level r0_mode r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_376 ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int)))) ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((r0_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2395 r0_group r0_level r0_mode r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair015_35 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := (((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) ∨ ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))))
abbrev formula_547 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := (shared_expr_Repair015_35 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)

theorem normalized_377 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2396 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : (formula_547 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ (((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)) := (or_congr (normalization_2378 r1_kind) (normalization_2394 r0_group r0_level r0_mode r1_group r1_level r1_mode))

abbrev shared_expr_Repair015_36 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := (((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ↔ (((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)))
theorem normalization_2397 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((formula_539 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ (formula_547 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) ↔ (shared_expr_Repair015_36 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := (iff_congr (normalization_2350 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (normalization_2396 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_514 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((formula_539 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ (formula_547 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) := by
  classical
  have ht := (normalized_377 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode) (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode))
  have n0 : ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_2385 r1_kind) (replay_512 r1_kind)
  have n1 : ((shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)) := by
    exact Iff.mp (normalization_2395 r0_group r0_level r0_mode r1_group r1_level r1_mode) (replay_513 r0_group r0_level r0_mode r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2397 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) hn

theorem normalized_378 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2398 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)) := (or_congr (normalization_2376 r1_kind) (or_congr (normalization_2377 r1_kind) (normalization_2394 r0_group r0_level r0_mode r1_group r1_level r1_mode)))

abbrev shared_expr_Repair015_37 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := ((((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)))
theorem normalization_2399 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((formula_547 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) ↔ (shared_expr_Repair015_37 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := (iff_congr (normalization_2396 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (normalization_2398 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_515 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((formula_547 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) := by
  classical
  have ht := (normalized_378 ((r1_kind) ≤ (0 : Int)) ((r1_kind) ≤ (-1 : Int)) (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode))
  have hn := ht
  exact Iff.mpr (normalization_2399 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) hn

theorem normalized_379 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair015_38 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := (((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)))
theorem normalization_2400 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((formula_539 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) ↔ (shared_expr_Repair015_38 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := (iff_congr (normalization_2350 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (normalization_2398 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))

-- Checked replay of trans.
theorem replay_516 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((formula_539 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ↔ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) := by
  classical
  have ht := (normalized_379 ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)))
  have n0 : (shared_expr_Repair015_36 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := by
    exact Iff.mp (normalization_2397 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (replay_514 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)
  have n1 : (shared_expr_Repair015_37 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := by
    exact Iff.mp (normalization_2399 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (replay_515 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2400 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) hn

theorem normalized_380 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2401 (r0_kind : Int) : ((r0_kind ≤ (2 : Int)) ∧ (r0_kind ≥ (2 : Int))) ↔ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) := (and_congr (normalization_2026 r0_kind) (normalization_2028 r0_kind))

theorem normalization_2402 (r0_kind : Int) : ((r0_kind = (2 : Int)) ↔ ((r0_kind ≤ (2 : Int)) ∧ (r0_kind ≥ (2 : Int)))) ↔ ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ↔ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) := (iff_congr (normalization_1506 r0_kind) (normalization_2401 r0_kind))

-- Checked replay of rewrite.
theorem replay_517 (r0_kind : Int) : ((r0_kind = (2 : Int)) ↔ ((r0_kind ≤ (2 : Int)) ∧ (r0_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_380 (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2402 r0_kind) hn

theorem normalized_381 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2403 (r0_kind : Int) : (((r0_kind ≤ (2 : Int)) ∧ (r0_kind ≥ (2 : Int))) ↔ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))))) ↔ ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_2401 r0_kind) (normalization_2031 r0_kind))

-- Checked replay of rewrite.
theorem replay_518 (r0_kind : Int) : (((r0_kind ≤ (2 : Int)) ∧ (r0_kind ≥ (2 : Int))) ↔ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_381 ((r0_kind) ≤ (2 : Int)) ((r0_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2403 r0_kind) hn

theorem normalized_382 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2404 (r0_kind : Int) : ((r0_kind = (2 : Int)) ↔ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))))) ↔ ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_1506 r0_kind) (normalization_2031 r0_kind))

-- Checked replay of trans.
theorem replay_519 (r0_kind : Int) : ((r0_kind = (2 : Int)) ↔ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_382 (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))))
  have n0 : ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ↔ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_2402 r0_kind) (replay_517 r0_kind)
  have n1 : ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2403 r0_kind) (replay_518 r0_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2404 r0_kind) hn

theorem normalized_383 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2405 (r0_kind : Int) : (¬ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))))) ↔ (¬ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) := (not_congr (normalization_2031 r0_kind))

theorem normalization_2406 (r0_kind : Int) : ((¬ (r0_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))))) ↔ ((¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))))) := (iff_congr (normalization_2320 r0_kind) (normalization_2405 r0_kind))

-- Checked replay of monotonicity.
theorem replay_520 (r0_kind : Int) : ((¬ (r0_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_383 (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))
  have n0 : ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2404 r0_kind) (replay_519 r0_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_2406 r0_kind) hn

theorem normalized_384 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2407 (r0_kind : Int) : ((¬ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))))) ↔ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) ↔ ((¬ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) ↔ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_2405 r0_kind) (normalization_2030 r0_kind))

-- Checked replay of rewrite.
theorem replay_521 (r0_kind : Int) : ((¬ (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))))) ↔ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_384 ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_2407 r0_kind) hn

theorem normalized_385 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2408 (r0_kind : Int) : ((¬ (r0_kind = (2 : Int))) ↔ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) ↔ ((¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ↔ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_2320 r0_kind) (normalization_2030 r0_kind))

-- Checked replay of trans.
theorem replay_522 (r0_kind : Int) : ((¬ (r0_kind = (2 : Int))) ↔ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_385 (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))
  have n0 : ((¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_2406 r0_kind) (replay_520 r0_kind)
  have n1 : ((¬ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) ↔ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_2407 r0_kind) (replay_521 r0_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2408 r0_kind) hn

abbrev shared_expr_Repair015_39 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((r1_kind = (2 : Int)) ∨ (formula_543 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) ↔ ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (formula_519 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
abbrev formula_548 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_39 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign)

theorem normalized_386 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : (((p0 ∧ (¬ p1)) ∨ (((p2 ∧ (¬ p3)) ∧ (((p4 ∧ (¬ p5)) ∧ ((p6 ∧ (¬ p7)) ∧ (p8 ∧ (¬ p9)))) ∨ ((¬ (p4 ∧ (¬ p5))) ∧ (¬ (¬ p5))))) ∨ ((¬ (p2 ∧ (¬ p3))) ∧ (((p3 ∧ (¬ p10)) ∧ ((((¬ p11) ∧ p12) ∧ (p6 ∧ (¬ p7))) ∨ ((¬ ((¬ p11) ∧ p12)) ∧ (¬ p12)))) ∨ ((¬ (p3 ∧ (¬ p10))) ∧ ((¬ (p13 ∧ (¬ p2))) ∨ ((((¬ p14) ∧ p15) ∧ (p8 ∧ (¬ p9))) ∨ ((¬ ((¬ p14) ∧ p15)) ∧ (¬ (¬ p14)))))))))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ ((((¬ p2) ∨ (¬ (¬ p3))) ∧ ((((¬ p3) ∨ (¬ (¬ p10))) ∧ ((¬ p13) ∨ (¬ (¬ p2)) ∨ ((((¬ (¬ p14)) ∨ (¬ p15)) ∧ (¬ (¬ p14))) ∨ ((¬ ((¬ (¬ p14)) ∨ (¬ p15))) ∧ (¬ ((¬ p8) ∨ (¬ (¬ p9)))))))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p10)))) ∧ ((((¬ (¬ p11)) ∨ (¬ p12)) ∧ (¬ p12)) ∨ ((¬ ((¬ (¬ p11)) ∨ (¬ p12))) ∧ (¬ ((¬ p6) ∨ (¬ (¬ p7))))))))) ∨ ((¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ ((((¬ p4) ∨ (¬ (¬ p5))) ∧ (¬ (¬ p5))) ∨ ((¬ ((¬ p4) ∨ (¬ (¬ p5)))) ∧ (¬ ((¬ (¬ p7)) ∨ (¬ (¬ p9)) ∨ (¬ p8) ∨ (¬ p6))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2409 (r1_kind : Int) : (r1_kind ≤ (2 : Int)) ↔ ((r1_kind) ≤ (2 : Int)) := by
  omega

theorem normalization_2410 (r1_kind : Int) : (¬ (r1_kind ≤ (2 : Int))) ↔ (¬ ((r1_kind) ≤ (2 : Int))) := (not_congr (normalization_2409 r1_kind))

theorem normalization_2411 (r1_kind : Int) : (r1_kind ≥ (2 : Int)) ↔ (¬ ((r1_kind) ≤ (1 : Int))) := by
  omega

theorem normalization_2412 (r1_kind : Int) : (¬ (r1_kind ≥ (2 : Int))) ↔ (¬ (¬ ((r1_kind) ≤ (1 : Int)))) := (not_congr (normalization_2411 r1_kind))

theorem normalization_2413 (r1_kind : Int) : ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))) ↔ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))) := (or_congr (normalization_2410 r1_kind) (normalization_2412 r1_kind))

theorem normalization_2414 (r1_kind : Int) : (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ↔ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) := (not_congr (normalization_2413 r1_kind))

theorem normalization_2415 (r0_depth r1_depth : Int) : ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ↔ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2416 (r0_depth r1_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (not_congr (normalization_2415 r0_depth r1_depth))

theorem normalization_2417 (r0_depth r1_depth : Int) : ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ↔ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2418 (r0_depth r1_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2417 r0_depth r1_depth))

theorem normalization_2419 (r0_depth r1_depth : Int) : ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))) ↔ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_2416 r0_depth r1_depth) (normalization_2418 r0_depth r1_depth))

theorem normalization_2420 (r0_depth r1_depth : Int) : ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ↔ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2421 (r0_depth r1_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := (not_congr (normalization_2420 r0_depth r1_depth))

theorem normalization_2422 (r0_depth r1_depth : Int) : ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (-1 : Int)) ↔ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_2423 (r0_depth r1_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_2422 r0_depth r1_depth))

theorem normalization_2424 (r0_depth r1_depth : Int) : ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_2421 r0_depth r1_depth) (normalization_2423 r0_depth r1_depth))

theorem normalization_2425 (r0_depth r1_depth : Int) : ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ↔ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_2426 (r0_depth r1_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ↔ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) := (not_congr (normalization_2425 r0_depth r1_depth))

theorem normalization_2427 (r0_depth r1_depth : Int) : ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (1 : Int)) ↔ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_2428 (r0_depth r1_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := (not_congr (normalization_2427 r0_depth r1_depth))

theorem normalization_2429 (r0_node r1_node : Int) : ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2430 (r0_node r1_node : Int) : (¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := (not_congr (normalization_2429 r0_node r1_node))

theorem normalization_2431 (r0_node r1_node : Int) : ((¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) := (or_congr (normalization_2363 r0_node r1_node) (normalization_2430 r0_node r1_node))

theorem normalization_2432 (r1_sign : Int) : (r1_sign ≤ (0 : Int)) ↔ ((r1_sign) ≤ (0 : Int)) := by
  omega

theorem normalization_2433 (r1_sign : Int) : (¬ (r1_sign ≤ (0 : Int))) ↔ (¬ ((r1_sign) ≤ (0 : Int))) := (not_congr (normalization_2432 r1_sign))

theorem normalization_2434 (r1_sign : Int) : (r1_sign ≥ (0 : Int)) ↔ (¬ ((r1_sign) ≤ (-1 : Int))) := by
  omega

theorem normalization_2435 (r1_sign : Int) : (¬ (r1_sign ≥ (0 : Int))) ↔ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))) := (not_congr (normalization_2434 r1_sign))

theorem normalization_2436 (r1_sign : Int) : ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))) ↔ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))) := (or_congr (normalization_2433 r1_sign) (normalization_2435 r1_sign))

theorem normalization_2437 (r1_sign : Int) : (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ↔ (¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) := (not_congr (normalization_2436 r1_sign))

abbrev shared_expr_Repair015_40 (r0_node r1_node : Int) : Prop := (((¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair015_41 (r0_node r1_node r1_sign : Int) : Prop := ((¬ ((¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))))
theorem normalization_2438 (r0_node r1_node r1_sign : Int) : (formula_515 r0_node r1_node r1_sign) ↔ ((shared_expr_Repair015_40 r0_node r1_node) ∨ (shared_expr_Repair015_41 r0_node r1_node r1_sign)) := (or_congr (and_congr (normalization_2431 r0_node r1_node) (normalization_2363 r0_node r1_node)) (and_congr (not_congr (normalization_2431 r0_node r1_node)) (normalization_2437 r1_sign)))

abbrev shared_expr_Repair015_42 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) ∨ ((shared_expr_Repair015_40 r0_node r1_node) ∨ (shared_expr_Repair015_41 r0_node r1_node r1_sign)))
theorem normalization_2439 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (1 : Int))) ∨ (formula_515 r0_node r1_node r1_sign)) ↔ (shared_expr_Repair015_42 r0_depth r0_node r1_depth r1_node r1_sign) := (or_congr (normalization_2426 r0_depth r1_depth) (or_congr (normalization_2428 r0_depth r1_depth) (normalization_2438 r0_node r1_node r1_sign)))

theorem normalization_2440 (r0_node r1_node : Int) : ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2441 (r0_node r1_node : Int) : (¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2440 r0_node r1_node))

theorem normalization_2442 (r0_node r1_node : Int) : ((¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) ∨ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)))) := (or_congr (normalization_2441 r0_node r1_node) (normalization_2357 r0_node r1_node))

abbrev shared_expr_Repair015_43 (r0_node r1_node : Int) : Prop := (((¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) ∨ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)))) ∧ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair015_44 (r0_node r0_sign r1_node : Int) : Prop := ((¬ ((¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) ∨ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))))
theorem normalization_2443 (r0_node r0_sign r1_node : Int) : (formula_516 r0_node r0_sign r1_node) ↔ ((shared_expr_Repair015_43 r0_node r1_node) ∨ (shared_expr_Repair015_44 r0_node r0_sign r1_node)) := (or_congr (and_congr (normalization_2442 r0_node r1_node) (normalization_2357 r0_node r1_node)) (and_congr (not_congr (normalization_2442 r0_node r1_node)) (normalization_2081 r0_sign)))

abbrev shared_expr_Repair015_45 (r0_depth r0_node r0_sign r1_depth r1_node : Int) : Prop := ((¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))))) ∧ ((shared_expr_Repair015_43 r0_node r1_node) ∨ (shared_expr_Repair015_44 r0_node r0_sign r1_node)))
abbrev shared_expr_Repair015_46 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair015_42 r0_depth r0_node r1_depth r1_node r1_sign)) ∨ (shared_expr_Repair015_45 r0_depth r0_node r0_sign r1_depth r1_node))
theorem normalization_2444 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : (formula_517 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Repair015_46 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2424 r0_depth r1_depth) (normalization_2439 r0_depth r0_node r1_depth r1_node r1_sign)) (and_congr (not_congr (normalization_2424 r0_depth r1_depth)) (normalization_2443 r0_node r0_sign r1_node)))

theorem normalization_2445 (r0_node r1_node : Int) : ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ↔ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2446 (r0_node r1_node : Int) : (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ↔ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := (not_congr (normalization_2445 r0_node r1_node))

theorem normalization_2447 (r0_node r1_node : Int) : ((¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int)))) ↔ ((¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) := (or_congr (normalization_2446 r0_node r1_node) (normalization_2352 r0_node r1_node))

theorem normalization_2448 (r0_sign r1_sign : Int) : ((¬ (r0_sign ≥ (1 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≤ (1 : Int)))) ↔ ((¬ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((r0_sign) ≤ (1 : Int)))) := (or_congr (normalization_2058 r0_sign) (or_congr (normalization_2435 r1_sign) (or_congr (normalization_2433 r1_sign) (normalization_2060 r0_sign))))

theorem normalization_2449 (r0_sign r1_sign : Int) : (¬ ((¬ (r0_sign ≥ (1 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≤ (1 : Int))))) ↔ (¬ ((¬ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((r0_sign) ≤ (1 : Int))))) := (not_congr (normalization_2448 r0_sign r1_sign))

abbrev shared_expr_Repair015_47 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((r0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair015_48 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((((¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_47 r0_node r0_sign r1_node r1_sign))
theorem normalization_2450 (r0_node r0_sign r1_node r1_sign : Int) : (formula_518 r0_node r0_sign r1_node r1_sign) ↔ (shared_expr_Repair015_48 r0_node r0_sign r1_node r1_sign) := (or_congr (and_congr (normalization_2447 r0_node r1_node) (normalization_2352 r0_node r1_node)) (and_congr (not_congr (normalization_2447 r0_node r1_node)) (normalization_2449 r0_sign r1_sign)))

abbrev shared_expr_Repair015_49 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair015_46 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) ∨ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair015_48 r0_node r0_sign r1_node r1_sign)))
theorem normalization_2451 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : (formula_519 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Repair015_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2419 r0_depth r1_depth) (normalization_2444 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) (and_congr (not_congr (normalization_2419 r0_depth r1_depth)) (normalization_2450 r0_node r0_sign r1_node r1_sign)))

theorem normalization_2452 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (formula_519 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) ↔ ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair015_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) := (or_congr (normalization_2414 r1_kind) (normalization_2451 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))

abbrev shared_expr_Repair015_50 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair015_27 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) ↔ ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair015_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
theorem normalization_2453 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_548 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair015_50 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := (iff_congr (normalization_2368 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (normalization_2452 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_523 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_548 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := by
  classical
  have ht := (normalized_386 ((r1_kind) ≤ (2 : Int)) ((r1_kind) ≤ (1 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) ((r0_sign) ≤ (1 : Int)) ((r0_sign) ≤ (0 : Int)) ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2453 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign) hn

abbrev shared_expr_Repair015_51 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) ∧ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))) ∧ ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (formula_519 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
abbrev formula_549 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_51 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_52 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((¬ (r1_kind = (0 : Int))) ∧ (¬ (r0_kind = (2 : Int))) ∧ ((r1_kind = (2 : Int)) ∨ (formula_543 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))) ↔ (formula_549 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))
abbrev formula_550 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_52 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)

theorem normalized_387 (p0 p1 p2 p3 p4 p5 : Prop) : ((((¬ p0) ↔ p1) ∧ ((¬ p2) ↔ p3) ∧ (p4 ↔ p5)) → (((¬ p0) ∧ (¬ p2) ∧ p4) ↔ (p1 ∧ p3 ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair015_53 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))) ∧ ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair015_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
theorem normalization_2454 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_549 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair015_53 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := (and_congr (normalization_2378 r1_kind) (and_congr (normalization_2030 r0_kind) (normalization_2452 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

theorem normalization_2455 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_550 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ ((shared_expr_Repair015_28 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair015_53 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)) := (iff_congr (normalization_2369 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (normalization_2454 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_524 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_550 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := by
  classical
  have ht := (normalized_387 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))) ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair015_27 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair015_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
  have n0 : ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ↔ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_2385 r1_kind) (replay_512 r1_kind)
  have n1 : ((¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ↔ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_2408 r0_kind) (replay_522 r0_kind)
  have n2 : (shared_expr_Repair015_50 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := by
    exact Iff.mp (normalization_2453 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (replay_523 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2455 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) hn

theorem normalized_388 (p0 p1 p2 : Prop) : ((p0 ∧ p1 ∧ p2) ↔ (¬ ((¬ p1) ∨ (¬ p0) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2456 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (¬ ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (formula_519 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))) ↔ (¬ ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair015_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))) := (not_congr (normalization_2452 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Repair015_54 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair015_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))))
theorem normalization_2457 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_2031 r0_kind) (or_congr (normalization_2379 r1_kind) (normalization_2456 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

theorem normalization_2458 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_2457 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))

theorem normalization_2459 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : ((formula_549 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) ↔ ((shared_expr_Repair015_53 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (¬ (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) := (iff_congr (normalization_2454 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (normalization_2458 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_525 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : ((formula_549 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) := by
  classical
  have ht := (normalized_388 ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))) ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (shared_expr_Repair015_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
  have hn := ht
  exact Iff.mpr (normalization_2459 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) hn

abbrev shared_expr_Repair015_55 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((¬ (r1_kind = (0 : Int))) ∧ (¬ (r0_kind = (2 : Int))) ∧ ((r1_kind = (2 : Int)) ∨ (formula_543 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))) ↔ (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))
abbrev formula_551 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_55 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)

theorem normalized_389 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2460 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_551 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ ((shared_expr_Repair015_28 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (¬ (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) := (iff_congr (normalization_2369 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (normalization_2458 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))

-- Checked replay of trans.
theorem replay_526 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_551 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := by
  classical
  have ht := (normalized_389 (shared_expr_Repair015_28 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (shared_expr_Repair015_53 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))
  have n0 : ((shared_expr_Repair015_28 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair015_53 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)) := by
    exact Iff.mp (normalization_2455 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (replay_524 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)
  have n1 : ((shared_expr_Repair015_53 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (¬ (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) := by
    exact Iff.mp (normalization_2459 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (replay_525 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2460 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) hn

abbrev shared_expr_Repair015_56 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∧ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) ∨ ((¬ (¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))))) ∧ (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))))
abbrev formula_552 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_56 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair015_57 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_544 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_552 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_553 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_57 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_390 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair015_58 (r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := ((¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int)))))) ∧ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)))
abbrev shared_expr_Repair015_59 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_58 r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode) ∨ ((¬ (¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))))) ∧ (¬ (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))))
theorem normalization_2461 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_552 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_59 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (and_congr (normalization_1673 r0_kind) (normalization_2398 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) (and_congr (not_congr (normalization_1673 r0_kind)) (normalization_2458 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair015_60 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_29 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_59 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2462 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_553 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_60 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_2370 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2461 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_527 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_553 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_390 (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))) ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair015_3 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (shared_expr_Repair015_28 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))
  have n0 : ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1675 r0_kind) (replay_316 r0_kind)
  have n1 : (shared_expr_Repair015_38 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := by
    exact Iff.mp (normalization_2400 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (replay_516 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)
  have n2 : ((shared_expr_Repair015_28 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (¬ (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) := by
    exact Iff.mp (normalization_2460 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (replay_526 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2462 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Repair015_61 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_552 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_524 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_554 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_61 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_391 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair015_62 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (¬ (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) ∨ (shared_expr_Repair015_58 r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode))
theorem normalization_2463 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_524 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_62 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (and_congr (normalization_1672 r0_kind) (normalization_2458 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)) (and_congr (not_congr (normalization_1672 r0_kind)) (normalization_2398 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)))

abbrev shared_expr_Repair015_63 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_59 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_62 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2464 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_554 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_63 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_2461 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2463 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_528 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_554 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_391 ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair015_34 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (shared_expr_Repair015_54 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_2464 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Repair015_64 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_544 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_524 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_555 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_64 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_392 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair015_65 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair015_29 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_62 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2465 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_555 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair015_65 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_2370 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2463 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of trans.
theorem replay_529 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_555 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_392 (shared_expr_Repair015_29 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair015_59 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair015_62 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : (shared_expr_Repair015_60 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
    exact Iff.mp (normalization_2462 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_527 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have n1 : (shared_expr_Repair015_63 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
    exact Iff.mp (normalization_2464 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_528 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2465 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_530 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_524 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_529 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_506 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33)

-- Checked replay of unit-resolution.
theorem replay_531 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : ((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∨ (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) := by
  exact (Or.elim (replay_500 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.inl l0)) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_530 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33)))))))

theorem propositional_393 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ ((((¬ p5) ∨ (¬ p6)) ∧ ((((¬ p7) ∨ (¬ p8)) ∧ ((¬ p9) ∨ (¬ p10) ∨ ((((¬ p11) ∨ (¬ p12)) ∧ (¬ p11)) ∨ ((¬ ((¬ p11) ∨ (¬ p12))) ∧ (¬ ((¬ p13) ∨ (¬ p14))))))) ∨ ((¬ ((¬ p7) ∨ (¬ p8))) ∧ ((((¬ p15) ∨ (¬ p16)) ∧ (¬ p16)) ∨ ((¬ ((¬ p15) ∨ (¬ p16))) ∧ (¬ ((¬ p17) ∨ (¬ p18)))))))) ∨ ((¬ ((¬ p5) ∨ (¬ p6))) ∧ ((((¬ p19) ∨ (¬ p20)) ∧ (¬ p20)) ∨ ((¬ ((¬ p19) ∨ (¬ p20))) ∧ (¬ ((¬ p18) ∨ (¬ p14) ∨ (¬ p13) ∨ (¬ p17)))))))))) ∨ p2) := by
  classical
  first | (by_cases case_p2 : p2 <;> simp [case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_532 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : ((formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ∨ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) := by
  exact (propositional_393 (r0_kind ≤ (2 : Int)) (r0_kind ≥ (2 : Int)) ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (-1 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (1 : Int)) ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) (r0_sign ≤ (1 : Int)) (r0_sign ≥ (1 : Int)) ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_533 (r1_node r2_node : Int) : ((¬ (r1_node ≥ (0 : Int))) ∨ (¬ (r2_node ≤ (0 : Int))) ∨ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair015_66 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))))
abbrev shared_expr_Repair015_67 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) ∨ (shared_expr_Repair015_66 r1_node r1_sign r2_node r2_sign))
abbrev formula_556 (r1_node r1_sign r2_node r2_sign : Int) : Prop := (shared_expr_Repair015_67 r1_node r1_sign r2_node r2_sign)

abbrev shared_expr_Repair015_68 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((¬ (formula_556 r1_node r1_sign r2_node r2_sign)) ∨ (¬ ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))))
abbrev formula_557 (r1_node r1_sign r2_node r2_sign : Int) : Prop := (shared_expr_Repair015_68 r1_node r1_sign r2_node r2_sign)

theorem propositional_394 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_534 (r1_node r1_sign r2_node r2_sign : Int) : (formula_557 r1_node r1_sign r2_node r2_sign) := by
  exact (propositional_394 ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)))

abbrev shared_expr_Repair015_69 (r1_node r2_node : Int) : Prop := (((¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))))
abbrev shared_expr_Repair015_70 (r1_node r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))))
abbrev formula_558 (r1_node r2_node r2_sign : Int) : Prop := ((shared_expr_Repair015_69 r1_node r2_node) ∨ (shared_expr_Repair015_70 r1_node r2_node r2_sign))

abbrev shared_expr_Repair015_71 (r1_node r2_node : Int) : Prop := (((¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))
abbrev shared_expr_Repair015_72 (r1_node r1_sign r2_node : Int) : Prop := ((¬ ((¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))))
abbrev formula_559 (r1_node r1_sign r2_node : Int) : Prop := ((shared_expr_Repair015_71 r1_node r2_node) ∨ (shared_expr_Repair015_72 r1_node r1_sign r2_node))

abbrev shared_expr_Repair015_73 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int)))) ∧ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_558 r1_node r2_node r2_sign)))
abbrev shared_expr_Repair015_74 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((shared_expr_Repair015_73 r1_depth r1_node r2_depth r2_node r2_sign) ∨ ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int))))) ∧ (formula_559 r1_node r1_sign r2_node)))
abbrev formula_560 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair015_74 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair015_75 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))) ∧ (formula_560 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ∨ ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) ∧ (formula_556 r1_node r1_sign r2_node r2_sign)))
abbrev formula_561 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair015_75 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair015_76 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((¬ (formula_561 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ∨ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))) ∨ (formula_556 r1_node r1_sign r2_node r2_sign))
abbrev formula_562 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair015_76 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

theorem propositional_395 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : ((¬ ((p0 ∧ ((((¬ p1) ∨ (¬ p2)) ∧ ((¬ p3) ∨ (¬ p4) ∨ ((((¬ p5) ∨ (¬ p6)) ∧ (¬ p5)) ∨ ((¬ ((¬ p5) ∨ (¬ p6))) ∧ (¬ ((¬ p7) ∨ (¬ p8))))))) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ ((((¬ p9) ∨ (¬ p10)) ∧ (¬ p10)) ∨ ((¬ ((¬ p9) ∨ (¬ p10))) ∧ (¬ ((¬ p11) ∨ (¬ p12)))))))) ∨ ((¬ p0) ∧ p13))) ∨ p0 ∨ p13) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_535 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_562 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := by
  exact (propositional_395 ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int)) ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (formula_556 r1_node r1_sign r2_node r2_sign))

abbrev shared_expr_Repair015_77 (r1_depth r2_depth : Int) : Prop := ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))
abbrev formula_563 (r1_depth r2_depth : Int) : Prop := (shared_expr_Repair015_77 r1_depth r2_depth)

theorem propositional_396 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_536 (r1_depth r2_depth : Int) : (formula_563 r1_depth r2_depth) := by
  exact (propositional_396 ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_537 (c0_level r1_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair015_78 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))))
abbrev formula_564 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair015_78 c0_level r1_depth r1_kind r1_sign)

theorem propositional_397 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_538 (c0_level r1_depth r1_kind r1_sign : Int) : ((formula_564 c0_level r1_depth r1_kind r1_sign) ∨ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))) := by
  exact (propositional_397 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)))

abbrev shared_expr_Repair015_79 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))))
abbrev formula_565 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair015_79 c0_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair015_80 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∧ (¬ (formula_564 c0_level r1_depth r1_kind r1_sign))) ∨ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∧ (¬ (formula_565 c0_level r1_depth r1_kind r1_sign))))
abbrev formula_566 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair015_80 c0_group c0_level r1_depth r1_kind r1_sign)

theorem propositional_398 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_539 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : ((¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ (formula_564 c0_level r1_depth r1_kind r1_sign))) := by
  exact (propositional_398 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (formula_564 c0_level r1_depth r1_kind r1_sign) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))

theorem propositional_399 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_540 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : (((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign))) ∨ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign)) := by
  exact (propositional_399 (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) (formula_566 c0_group c0_level r1_depth r1_kind r1_sign))

abbrev shared_expr_Repair015_81 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))))
abbrev formula_567 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair015_81 c0_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair015_82 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))))
abbrev formula_568 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair015_82 c0_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair015_83 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∧ (¬ (formula_567 c0_level r1_depth r1_kind r1_sign))) ∨ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∧ (¬ (formula_568 c0_level r1_depth r1_kind r1_sign))))
abbrev formula_569 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair015_83 c0_group c0_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair015_84 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_node % (2 : Int)) ≤ (0 : Int))))
abbrev formula_570 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_84 c0_level r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_85 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∧ (¬ (formula_570 c0_level r1_depth r1_kind r1_node r1_sign))))
abbrev formula_571 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_85 c0_group c0_level r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_86 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_node % (2 : Int)) ≥ (1 : Int))))
abbrev formula_572 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_86 c0_level r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_87 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∧ (¬ (formula_572 c0_level r1_depth r1_kind r1_node r1_sign))))
abbrev formula_573 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_87 c0_group c0_level r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_88 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_node % (2 : Int)) ≤ (0 : Int))))
abbrev formula_574 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_88 c0_level r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_89 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∧ (¬ (formula_574 c0_level r1_depth r1_kind r1_node r1_sign))))
abbrev formula_575 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_89 c0_group c0_level r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_90 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_node % (2 : Int)) ≥ (1 : Int))))
abbrev formula_576 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_90 c0_level r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_91 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∧ (¬ (formula_576 c0_level r1_depth r1_kind r1_node r1_sign))))
abbrev formula_577 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_91 c0_group c0_level r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_92 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_571 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_573 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_575 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_577 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))))
abbrev formula_578 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_92 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair015_93 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ (¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_571 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_573 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_575 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_577 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))))
abbrev formula_579 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair015_93 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)

theorem propositional_400 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_541 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (formula_579 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) := by
  exact (propositional_400 ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign))) ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign))) ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_571 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_573 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_575 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_577 c0_group c0_level r1_depth r1_kind r1_node r1_sign))))

end H4Formal.Generated.Repair
