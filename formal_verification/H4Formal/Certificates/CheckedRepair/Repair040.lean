import H4Formal.Certificates.CheckedRepair.Repair039

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair040_0 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ∧ ((c0_node % (2 : Int)) ≤ (0 : Int)))
abbrev formula_974 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := (shared_expr_Repair040_0 c0_depth c0_kind c0_node c0_sign r1_level)

theorem normalized_929 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ (¬ p7))) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ (¬ p7)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_1 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ∧ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
theorem normalization_3592 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_974 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_1 c0_depth c0_kind c0_node c0_sign r1_level) := (and_congr (normalization_3495 c0_kind) (and_congr (normalization_3579 c0_depth r1_level) (and_congr (normalization_468 c0_sign) (normalization_508 c0_node))))

abbrev shared_expr_Repair040_2 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3593 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int))) ↔ (formula_974 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ ((shared_expr_Repair040_2 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_1 c0_depth c0_kind c0_node c0_sign r1_level)) := (iff_congr (normalization_3315 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3592 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair040_3 (c0_depth r1_level : Int) : Prop := ((((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))))
abbrev shared_expr_Repair040_4 (c0_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
abbrev shared_expr_Repair040_5 (c0_node : Int) : Prop := (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
theorem replay_2420 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int))) ↔ (formula_974 c0_depth c0_kind c0_node c0_sign r1_level)) := by
  classical
  have ht := (normalized_929 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))) (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have n0 : ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3497 c0_kind) (replay_2377 c0_kind)
  have n1 : (shared_expr_Repair040_3 c0_depth r1_level) := by
    exact Iff.mp (normalization_3582 c0_depth r1_level) (replay_2413 c0_depth r1_level)
  have n2 : (shared_expr_Repair040_4 c0_sign) := by
    exact Iff.mp (normalization_3508 c0_sign) (replay_2381 c0_sign)
  have n3 : (shared_expr_Repair040_5 c0_node) := by
    exact Iff.mp (normalization_3591 c0_node) (replay_2419 c0_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_3593 c0_depth c0_kind c0_node c0_sign r1_level) hn

theorem normalized_930 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ (¬ p5)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_6 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_3594 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_881 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level) := (or_congr (normalization_453 c0_kind) (or_congr (normalization_455 c0_kind) (or_congr (normalization_469 c0_sign) (or_congr (normalization_509 c0_node) (or_congr (normalization_3576 c0_depth r1_level) (normalization_3577 c0_depth r1_level))))))

theorem normalization_3595 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (¬ (formula_881 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ (¬ (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level)) := (not_congr (normalization_3594 c0_depth c0_kind c0_node c0_sign r1_level))

theorem normalization_3596 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : ((formula_974 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (formula_881 c0_depth c0_kind c0_node c0_sign r1_level))) ↔ ((shared_expr_Repair040_1 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))) := (iff_congr (normalization_3592 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3595 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of rewrite.
theorem replay_2421 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : ((formula_974 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (formula_881 c0_depth c0_kind c0_node c0_sign r1_level))) := by
  classical
  have ht := (normalized_930 ((c0_kind) ≤ (1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3596 c0_depth c0_kind c0_node c0_sign r1_level) hn

theorem normalized_931 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3597 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int))) ↔ (¬ (formula_881 c0_depth c0_kind c0_node c0_sign r1_level))) ↔ ((shared_expr_Repair040_2 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))) := (iff_congr (normalization_3315 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3595 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of trans.
theorem replay_2422 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int))) ↔ (¬ (formula_881 c0_depth c0_kind c0_node c0_sign r1_level))) := by
  classical
  have ht := (normalized_931 (shared_expr_Repair040_2 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_1 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))
  have n0 : ((shared_expr_Repair040_2 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_1 c0_depth c0_kind c0_node c0_sign r1_level)) := by
    exact Iff.mp (normalization_3593 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2420 c0_depth c0_kind c0_node c0_sign r1_level)
  have n1 : ((shared_expr_Repair040_1 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))) := by
    exact Iff.mp (normalization_3596 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2421 c0_depth c0_kind c0_node c0_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3597 c0_depth c0_kind c0_node c0_sign r1_level) hn

abbrev shared_expr_Repair040_7 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_877 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_881 c0_depth c0_kind c0_node c0_sign r1_level))))
abbrev formula_975 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair040_7 c0_depth c0_kind c0_node c0_sign r1_group r1_level)

theorem normalized_932 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_8 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
abbrev shared_expr_Repair040_9 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))))
theorem normalization_3598 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_975 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_9 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_3512 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_3595 c0_depth c0_kind c0_node c0_sign r1_level)))

abbrev shared_expr_Repair040_10 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair040_11 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair040_10 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair040_2 c0_depth c0_kind c0_node c0_sign r1_level)))
theorem normalization_3599 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_975 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_9 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3382 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3598 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_2423 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_975 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_932 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair040_10 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair040_2 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((shared_expr_Repair040_10 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level))) := by
    exact Iff.mp (normalization_3514 c0_depth c0_kind c0_sign r1_level) (replay_2384 c0_depth c0_kind c0_sign r1_level)
  have n2 : ((shared_expr_Repair040_2 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))) := by
    exact Iff.mp (normalization_3597 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2422 c0_depth c0_kind c0_node c0_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3599 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

theorem normalized_933 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_12 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level))))
theorem normalization_3600 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_3595 c0_depth c0_kind c0_node c0_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_3512 c0_depth c0_kind c0_sign r1_level)))

theorem normalization_3601 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_975 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_9 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3598 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3600 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_2424 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_975 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_933 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair040_6 c0_depth c0_kind c0_node c0_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3601 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

theorem normalized_934 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3602 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3382 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3600 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_2425 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_934 (shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_9 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_9 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3599 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2423 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair040_9 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3601 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2424 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3602 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

abbrev shared_expr_Repair040_13 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (2 : Int)) ∧ (formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))))) ∧ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
abbrev formula_976 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_13 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_935 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3603 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))))) ∧ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (and_congr (normalization_3563 r1_mode) (normalization_3600 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

abbrev shared_expr_Repair040_14 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
theorem normalization_3604 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_976 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_14 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3383 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3603 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_2426 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_976 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_935 (((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))) (shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3565 r1_mode) (replay_2406 r1_mode)
  have n1 : ((shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3602 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2425 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3604 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair040_15 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))))) ∧ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
abbrev formula_977 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_15 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_936 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3605 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (not_congr (normalization_3600 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

theorem normalization_3606 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := (or_congr (normalization_3560 r1_mode) (or_congr (normalization_3561 r1_mode) (normalization_3605 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))

theorem normalization_3607 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) := (not_congr (normalization_3606 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

abbrev shared_expr_Repair040_16 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
theorem normalization_3608 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_977 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_16 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3603 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3607 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_2427 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_977 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_936 ((r1_mode) ≤ (2 : Int)) ((r1_mode) ≤ (1 : Int)) (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3608 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair040_17 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (2 : Int)) ∧ (formula_942 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
abbrev formula_978 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_17 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_937 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_18 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
theorem normalization_3609 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_978 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_18 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3383 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3607 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_2428 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_978 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_937 ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair040_11 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ((¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair040_12 c0_depth c0_kind c0_node c0_sign r1_group r1_level))))
  have n0 : (shared_expr_Repair040_14 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3604 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (replay_2426 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Repair040_16 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3608 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (replay_2427 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3609 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

theorem normalized_938 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3610 (r1_mode : Int) : (r1_mode ≤ (3 : Int)) ↔ ((r1_mode) ≤ (3 : Int)) := by
  omega

theorem normalization_3611 (r1_mode : Int) : (r1_mode ≥ (3 : Int)) ↔ (¬ ((r1_mode) ≤ (2 : Int))) := by
  omega

theorem normalization_3612 (r1_mode : Int) : ((r1_mode ≤ (3 : Int)) ∧ (r1_mode ≥ (3 : Int))) ↔ (((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) := (and_congr (normalization_3610 r1_mode) (normalization_3611 r1_mode))

theorem normalization_3613 (r1_mode : Int) : ((r1_mode = (3 : Int)) ↔ ((r1_mode ≤ (3 : Int)) ∧ (r1_mode ≥ (3 : Int)))) ↔ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ↔ (((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int))))) := (iff_congr (normalization_3240 r1_mode) (normalization_3612 r1_mode))

-- Checked replay of rewrite.
theorem replay_2429 (r1_mode : Int) : ((r1_mode = (3 : Int)) ↔ ((r1_mode ≤ (3 : Int)) ∧ (r1_mode ≥ (3 : Int)))) := by
  classical
  have ht := (normalized_938 (((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3613 r1_mode) hn

theorem normalized_939 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3614 (r1_mode : Int) : (¬ (r1_mode ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int))) := (not_congr (normalization_3610 r1_mode))

theorem normalization_3615 (r1_mode : Int) : (¬ (r1_mode ≥ (3 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) := (not_congr (normalization_3611 r1_mode))

theorem normalization_3616 (r1_mode : Int) : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int)))) ↔ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))) := (or_congr (normalization_3614 r1_mode) (normalization_3615 r1_mode))

theorem normalization_3617 (r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))))) := (not_congr (normalization_3616 r1_mode))

theorem normalization_3618 (r1_mode : Int) : (((r1_mode ≤ (3 : Int)) ∧ (r1_mode ≥ (3 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int)))))) ↔ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))))) := (iff_congr (normalization_3612 r1_mode) (normalization_3617 r1_mode))

-- Checked replay of rewrite.
theorem replay_2430 (r1_mode : Int) : (((r1_mode ≤ (3 : Int)) ∧ (r1_mode ≥ (3 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int)))))) := by
  classical
  have ht := (normalized_939 ((r1_mode) ≤ (3 : Int)) ((r1_mode) ≤ (2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3618 r1_mode) hn

theorem normalized_940 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3619 (r1_mode : Int) : ((r1_mode = (3 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int)))))) ↔ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))))) := (iff_congr (normalization_3240 r1_mode) (normalization_3617 r1_mode))

-- Checked replay of trans.
theorem replay_2431 (r1_mode : Int) : ((r1_mode = (3 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int)))))) := by
  classical
  have ht := (normalized_940 (((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))))))
  have n0 : ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ↔ (((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int))))) := by
    exact Iff.mp (normalization_3613 r1_mode) (replay_2429 r1_mode)
  have n1 : ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))))) := by
    exact Iff.mp (normalization_3618 r1_mode) (replay_2430 r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3619 r1_mode) hn

theorem normalized_941 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3620 (c0_node : Int) : ((c0_node % (2 : Int)) ≤ (1 : Int)) ↔ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) := by
  omega

theorem normalization_3621 (c0_node : Int) : (((c0_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := (and_congr (normalization_3620 c0_node) (normalization_524 c0_node))

abbrev shared_expr_Repair040_19 (c0_node : Int) : Prop := (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ↔ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
theorem normalization_3622 (c0_node : Int) : (((c0_node % (2 : Int)) = (1 : Int)) ↔ (((c0_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int)))) ↔ (shared_expr_Repair040_19 c0_node) := (iff_congr (normalization_164 c0_node) (normalization_3621 c0_node))

-- Checked replay of rewrite.
theorem replay_2432 (c0_node : Int) : (((c0_node % (2 : Int)) = (1 : Int)) ↔ (((c0_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_941 ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3622 c0_node) hn

-- Checked replay of rewrite.
theorem replay_2433 (c0_node : Int) : (((c0_node % (2 : Int)) ≤ (1 : Int)) ↔ True) := by
  classical
  first | omega | grind (splits := 40)

theorem normalized_942 (p0 p1 : Prop) : ((((¬ p0) ↔ True)) → (((¬ p0) ∧ p1) ↔ (True ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3623 (c0_node : Int) : (((c0_node % (2 : Int)) ≤ (1 : Int)) ↔ True) ↔ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ↔ True) := (iff_congr (normalization_3620 c0_node) (normalization_305))

theorem normalization_3624 (c0_node : Int) : (True ∧ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := (and_congr (normalization_305) (normalization_524 c0_node))

abbrev shared_expr_Repair040_20 (c0_node : Int) : Prop := (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ↔ (True ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
theorem normalization_3625 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((c0_node % (2 : Int)) ≥ (1 : Int)))) ↔ (shared_expr_Repair040_20 c0_node) := (iff_congr (normalization_3621 c0_node) (normalization_3624 c0_node))

-- Checked replay of monotonicity.
theorem replay_2434 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((c0_node % (2 : Int)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_942 ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int)) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have n0 : ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ↔ True) := by
    exact Iff.mp (normalization_3623 c0_node) (replay_2433 c0_node)
  have hn := ht n0
  exact Iff.mpr (normalization_3625 c0_node) hn

theorem normalized_943 (p0 : Prop) : ((True ∧ p0) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3626 (c0_node : Int) : ((True ∧ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ ((True ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := (iff_congr (normalization_3624 c0_node) (normalization_524 c0_node))

-- Checked replay of rewrite.
theorem replay_2435 (c0_node : Int) : ((True ∧ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c0_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_943 ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3626 c0_node) hn

theorem normalized_944 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_21 (c0_node : Int) : Prop := (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
theorem normalization_3627 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ (shared_expr_Repair040_21 c0_node) := (iff_congr (normalization_3621 c0_node) (normalization_524 c0_node))

-- Checked replay of trans.
theorem replay_2436 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c0_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_944 ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) (True ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair040_20 c0_node) := by
    exact Iff.mp (normalization_3625 c0_node) (replay_2434 c0_node)
  have n1 : ((True ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
    exact Iff.mp (normalization_3626 c0_node) (replay_2435 c0_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3627 c0_node) hn

theorem normalized_945 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3628 (c0_node : Int) : (((c0_node % (2 : Int)) = (1 : Int)) ↔ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ (shared_expr_Repair040_21 c0_node) := (iff_congr (normalization_164 c0_node) (normalization_524 c0_node))

-- Checked replay of trans.
theorem replay_2437 (c0_node : Int) : (((c0_node % (2 : Int)) = (1 : Int)) ↔ ((c0_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_945 ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) (shared_expr_Repair040_21 c0_node))
  have n0 : (shared_expr_Repair040_19 c0_node) := by
    exact Iff.mp (normalization_3622 c0_node) (replay_2432 c0_node)
  have n1 : (shared_expr_Repair040_21 c0_node) := by
    exact Iff.mp (normalization_3627 c0_node) (replay_2436 c0_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3628 c0_node) hn

abbrev shared_expr_Repair040_22 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int)))
abbrev formula_979 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := (shared_expr_Repair040_22 c0_depth c0_kind c0_node c0_sign r1_level)

theorem normalized_946 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ p7)) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ p7))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_23 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
theorem normalization_3629 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_979 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_23 c0_depth c0_kind c0_node c0_sign r1_level) := (and_congr (normalization_3495 c0_kind) (and_congr (normalization_3579 c0_depth r1_level) (and_congr (normalization_468 c0_sign) (normalization_524 c0_node))))

abbrev shared_expr_Repair040_24 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
theorem normalization_3630 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int))) ↔ (formula_979 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ ((shared_expr_Repair040_24 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_23 c0_depth c0_kind c0_node c0_sign r1_level)) := (iff_congr (normalization_3318 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3629 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of monotonicity.
theorem replay_2438 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int))) ↔ (formula_979 c0_depth c0_kind c0_node c0_sign r1_level)) := by
  classical
  have ht := (normalized_946 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))) (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have n0 : ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3497 c0_kind) (replay_2377 c0_kind)
  have n1 : (shared_expr_Repair040_3 c0_depth r1_level) := by
    exact Iff.mp (normalization_3582 c0_depth r1_level) (replay_2413 c0_depth r1_level)
  have n2 : (shared_expr_Repair040_4 c0_sign) := by
    exact Iff.mp (normalization_3508 c0_sign) (replay_2381 c0_sign)
  have n3 : (shared_expr_Repair040_21 c0_node) := by
    exact Iff.mp (normalization_3628 c0_node) (replay_2437 c0_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_3630 c0_depth c0_kind c0_node c0_sign r1_level) hn

theorem normalized_947 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ p5) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_25 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_3631 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_883 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level) := (or_congr (normalization_453 c0_kind) (or_congr (normalization_455 c0_kind) (or_congr (normalization_469 c0_sign) (or_congr (normalization_525 c0_node) (or_congr (normalization_3576 c0_depth r1_level) (normalization_3577 c0_depth r1_level))))))

theorem normalization_3632 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (¬ (formula_883 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ (¬ (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level)) := (not_congr (normalization_3631 c0_depth c0_kind c0_node c0_sign r1_level))

theorem normalization_3633 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : ((formula_979 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (formula_883 c0_depth c0_kind c0_node c0_sign r1_level))) ↔ ((shared_expr_Repair040_23 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))) := (iff_congr (normalization_3629 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3632 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of rewrite.
theorem replay_2439 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : ((formula_979 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (formula_883 c0_depth c0_kind c0_node c0_sign r1_level))) := by
  classical
  have ht := (normalized_947 ((c0_kind) ≤ (1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3633 c0_depth c0_kind c0_node c0_sign r1_level) hn

theorem normalized_948 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3634 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int))) ↔ (¬ (formula_883 c0_depth c0_kind c0_node c0_sign r1_level))) ↔ ((shared_expr_Repair040_24 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))) := (iff_congr (normalization_3318 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3632 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of trans.
theorem replay_2440 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int))) ↔ (¬ (formula_883 c0_depth c0_kind c0_node c0_sign r1_level))) := by
  classical
  have ht := (normalized_948 (shared_expr_Repair040_24 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_23 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))
  have n0 : ((shared_expr_Repair040_24 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_23 c0_depth c0_kind c0_node c0_sign r1_level)) := by
    exact Iff.mp (normalization_3630 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2438 c0_depth c0_kind c0_node c0_sign r1_level)
  have n1 : ((shared_expr_Repair040_23 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))) := by
    exact Iff.mp (normalization_3633 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2439 c0_depth c0_kind c0_node c0_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3634 c0_depth c0_kind c0_node c0_sign r1_level) hn

abbrev shared_expr_Repair040_26 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_877 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_883 c0_depth c0_kind c0_node c0_sign r1_level))))
abbrev formula_980 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair040_26 c0_depth c0_kind c0_node c0_sign r1_group r1_level)

theorem normalized_949 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_27 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))))
theorem normalization_3635 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_980 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_27 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_3512 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_3632 c0_depth c0_kind c0_node c0_sign r1_level)))

abbrev shared_expr_Repair040_28 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair040_10 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair040_24 c0_depth c0_kind c0_node c0_sign r1_level)))
theorem normalization_3636 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_980 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_27 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3384 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3635 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_2441 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_980 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_949 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair040_10 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair040_24 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((shared_expr_Repair040_10 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level))) := by
    exact Iff.mp (normalization_3514 c0_depth c0_kind c0_sign r1_level) (replay_2384 c0_depth c0_kind c0_sign r1_level)
  have n2 : ((shared_expr_Repair040_24 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))) := by
    exact Iff.mp (normalization_3634 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2440 c0_depth c0_kind c0_node c0_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3636 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

theorem normalized_950 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_29 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level))))
theorem normalization_3637 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_3632 c0_depth c0_kind c0_node c0_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_3512 c0_depth c0_kind c0_sign r1_level)))

theorem normalization_3638 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_980 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_27 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3635 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3637 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_2442 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_980 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_950 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair040_8 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair040_25 c0_depth c0_kind c0_node c0_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3638 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

theorem normalized_951 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3639 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3384 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3637 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_2443 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_951 (shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_27 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_27 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3636 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2441 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair040_27 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3638 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2442 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3639 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

abbrev shared_expr_Repair040_30 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (3 : Int)) ∧ (formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))))) ∧ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
abbrev formula_981 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_30 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_952 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3640 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))))) ∧ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (and_congr (normalization_3617 r1_mode) (normalization_3637 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

abbrev shared_expr_Repair040_31 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
theorem normalization_3641 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_981 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3385 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3640 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_2444 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_981 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_952 (((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))) (shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))))) := by
    exact Iff.mp (normalization_3619 r1_mode) (replay_2431 r1_mode)
  have n1 : ((shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3639 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2443 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3641 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair040_32 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))))) ∧ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
abbrev formula_982 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_32 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_953 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3642 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (not_congr (normalization_3637 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

theorem normalization_3643 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := (or_congr (normalization_3614 r1_mode) (or_congr (normalization_3615 r1_mode) (normalization_3642 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))

theorem normalization_3644 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) := (not_congr (normalization_3643 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

abbrev shared_expr_Repair040_33 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
theorem normalization_3645 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_982 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_33 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3640 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3644 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_2445 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_982 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_953 ((r1_mode) ≤ (3 : Int)) ((r1_mode) ≤ (2 : Int)) (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3645 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair040_34 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (3 : Int)) ∧ (formula_943 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
abbrev formula_983 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_34 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_954 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_35 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
theorem normalization_3646 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_983 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_35 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3385 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3644 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_2446 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_983 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_954 ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair040_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair040_29 c0_depth c0_kind c0_node c0_sign r1_group r1_level))))
  have n0 : (shared_expr_Repair040_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3641 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (replay_2444 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Repair040_33 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3645 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (replay_2445 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3646 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

theorem normalized_955 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3647 (r1_mode : Int) : (r1_mode ≤ (4 : Int)) ↔ ((r1_mode) ≤ (4 : Int)) := by
  omega

theorem normalization_3648 (r1_mode : Int) : ((r1_mode ≤ (4 : Int)) ∧ (r1_mode ≥ (4 : Int))) ↔ (((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) := (and_congr (normalization_3647 r1_mode) (normalization_2271 r1_mode))

theorem normalization_3649 (r1_mode : Int) : ((r1_mode = (4 : Int)) ↔ ((r1_mode ≤ (4 : Int)) ∧ (r1_mode ≥ (4 : Int)))) ↔ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ↔ (((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int))))) := (iff_congr (normalization_3244 r1_mode) (normalization_3648 r1_mode))

-- Checked replay of rewrite.
theorem replay_2447 (r1_mode : Int) : ((r1_mode = (4 : Int)) ↔ ((r1_mode ≤ (4 : Int)) ∧ (r1_mode ≥ (4 : Int)))) := by
  classical
  have ht := (normalized_955 (((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3649 r1_mode) hn

theorem normalized_956 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3650 (r1_mode : Int) : (¬ (r1_mode ≤ (4 : Int))) ↔ (¬ ((r1_mode) ≤ (4 : Int))) := (not_congr (normalization_3647 r1_mode))

theorem normalization_3651 (r1_mode : Int) : (¬ (r1_mode ≥ (4 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) := (not_congr (normalization_2271 r1_mode))

theorem normalization_3652 (r1_mode : Int) : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int)))) ↔ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int))))) := (or_congr (normalization_3650 r1_mode) (normalization_3651 r1_mode))

theorem normalization_3653 (r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))))) := (not_congr (normalization_3652 r1_mode))

theorem normalization_3654 (r1_mode : Int) : (((r1_mode ≤ (4 : Int)) ∧ (r1_mode ≥ (4 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int)))))) ↔ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int))))))) := (iff_congr (normalization_3648 r1_mode) (normalization_3653 r1_mode))

-- Checked replay of rewrite.
theorem replay_2448 (r1_mode : Int) : (((r1_mode ≤ (4 : Int)) ∧ (r1_mode ≥ (4 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int)))))) := by
  classical
  have ht := (normalized_956 ((r1_mode) ≤ (4 : Int)) ((r1_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3654 r1_mode) hn

theorem normalized_957 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3655 (r1_mode : Int) : ((r1_mode = (4 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int)))))) ↔ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int))))))) := (iff_congr (normalization_3244 r1_mode) (normalization_3653 r1_mode))

-- Checked replay of trans.
theorem replay_2449 (r1_mode : Int) : ((r1_mode = (4 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int)))))) := by
  classical
  have ht := (normalized_957 (((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int))))))))
  have n0 : ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ↔ (((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int))))) := by
    exact Iff.mp (normalization_3649 r1_mode) (replay_2447 r1_mode)
  have n1 : ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int))))))) := by
    exact Iff.mp (normalization_3654 r1_mode) (replay_2448 r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3655 r1_mode) hn

abbrev shared_expr_Repair040_36 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ∧ ((c0_node % (2 : Int)) ≤ (0 : Int)))
abbrev formula_984 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := (shared_expr_Repair040_36 c0_depth c0_kind c0_node c0_sign r1_level)

theorem normalized_958 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ (¬ p7))) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ (¬ p7)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_37 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ∧ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
theorem normalization_3656 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_984 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_37 c0_depth c0_kind c0_node c0_sign r1_level) := (and_congr (normalization_3495 c0_kind) (and_congr (normalization_3579 c0_depth r1_level) (and_congr (normalization_496 c0_sign) (normalization_508 c0_node))))

abbrev shared_expr_Repair040_38 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3657 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int))) ↔ (formula_984 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ ((shared_expr_Repair040_38 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_37 c0_depth c0_kind c0_node c0_sign r1_level)) := (iff_congr (normalization_3321 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3656 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair040_39 (c0_sign : Int) : Prop := (((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
theorem replay_2450 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int))) ↔ (formula_984 c0_depth c0_kind c0_node c0_sign r1_level)) := by
  classical
  have ht := (normalized_958 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))) (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have n0 : ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3497 c0_kind) (replay_2377 c0_kind)
  have n1 : (shared_expr_Repair040_3 c0_depth r1_level) := by
    exact Iff.mp (normalization_3582 c0_depth r1_level) (replay_2413 c0_depth r1_level)
  have n2 : (shared_expr_Repair040_39 c0_sign) := by
    exact Iff.mp (normalization_3537 c0_sign) (replay_2394 c0_sign)
  have n3 : (shared_expr_Repair040_5 c0_node) := by
    exact Iff.mp (normalization_3591 c0_node) (replay_2419 c0_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_3657 c0_depth c0_kind c0_node c0_sign r1_level) hn

theorem normalized_959 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ (¬ p5)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_40 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_3658 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_885 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level) := (or_congr (normalization_453 c0_kind) (or_congr (normalization_455 c0_kind) (or_congr (normalization_497 c0_sign) (or_congr (normalization_509 c0_node) (or_congr (normalization_3576 c0_depth r1_level) (normalization_3577 c0_depth r1_level))))))

theorem normalization_3659 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (¬ (formula_885 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ (¬ (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level)) := (not_congr (normalization_3658 c0_depth c0_kind c0_node c0_sign r1_level))

theorem normalization_3660 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : ((formula_984 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (formula_885 c0_depth c0_kind c0_node c0_sign r1_level))) ↔ ((shared_expr_Repair040_37 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level))) := (iff_congr (normalization_3656 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3659 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of rewrite.
theorem replay_2451 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : ((formula_984 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (formula_885 c0_depth c0_kind c0_node c0_sign r1_level))) := by
  classical
  have ht := (normalized_959 ((c0_kind) ≤ (1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3660 c0_depth c0_kind c0_node c0_sign r1_level) hn

theorem normalized_960 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3661 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int))) ↔ (¬ (formula_885 c0_depth c0_kind c0_node c0_sign r1_level))) ↔ ((shared_expr_Repair040_38 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level))) := (iff_congr (normalization_3321 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3659 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of trans.
theorem replay_2452 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (0 : Int))) ↔ (¬ (formula_885 c0_depth c0_kind c0_node c0_sign r1_level))) := by
  classical
  have ht := (normalized_960 (shared_expr_Repair040_38 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_37 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level))
  have n0 : ((shared_expr_Repair040_38 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_37 c0_depth c0_kind c0_node c0_sign r1_level)) := by
    exact Iff.mp (normalization_3657 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2450 c0_depth c0_kind c0_node c0_sign r1_level)
  have n1 : ((shared_expr_Repair040_37 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level))) := by
    exact Iff.mp (normalization_3660 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2451 c0_depth c0_kind c0_node c0_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3661 c0_depth c0_kind c0_node c0_sign r1_level) hn

abbrev shared_expr_Repair040_41 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_885 c0_depth c0_kind c0_node c0_sign r1_level))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_879 c0_depth c0_kind c0_sign r1_level))))
abbrev formula_985 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair040_41 c0_depth c0_kind c0_node c0_sign r1_group r1_level)

theorem normalized_961 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_42 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
abbrev shared_expr_Repair040_43 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))))
theorem normalization_3662 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_985 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_43 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_3659 c0_depth c0_kind c0_node c0_sign r1_level)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_3541 c0_depth c0_kind c0_sign r1_level)))

abbrev shared_expr_Repair040_44 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair040_45 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair040_38 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair040_44 c0_depth c0_kind c0_sign r1_level)))
theorem normalization_3663 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_985 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_43 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3386 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3662 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_2453 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_985 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_961 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair040_38 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_44 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((shared_expr_Repair040_38 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level))) := by
    exact Iff.mp (normalization_3661 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2452 c0_depth c0_kind c0_node c0_sign r1_level)
  have n2 : ((shared_expr_Repair040_44 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))) := by
    exact Iff.mp (normalization_3543 c0_depth c0_kind c0_sign r1_level) (replay_2397 c0_depth c0_kind c0_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3663 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

theorem normalized_962 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_46 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level))))
theorem normalization_3664 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_3541 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_3659 c0_depth c0_kind c0_node c0_sign r1_level)))

theorem normalization_3665 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_985 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_43 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3662 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3664 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_2454 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_985 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_962 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair040_40 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3665 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

theorem normalized_963 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3666 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3386 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3664 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_2455 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_963 (shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_43 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_43 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3663 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2453 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair040_43 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3665 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2454 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3666 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

abbrev shared_expr_Repair040_47 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (4 : Int)) ∧ (formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))))) ∧ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
abbrev formula_986 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_47 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_964 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3667 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))))) ∧ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (and_congr (normalization_3653 r1_mode) (normalization_3664 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

abbrev shared_expr_Repair040_48 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
theorem normalization_3668 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_986 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_48 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3387 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3667 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_2456 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_986 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_964 (((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int))))) (shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int))))))) := by
    exact Iff.mp (normalization_3655 r1_mode) (replay_2449 r1_mode)
  have n1 : ((shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3666 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2455 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3668 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair040_49 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))))) ∧ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
abbrev formula_987 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_49 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_965 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3669 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (not_congr (normalization_3664 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

theorem normalization_3670 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := (or_congr (normalization_3650 r1_mode) (or_congr (normalization_3651 r1_mode) (normalization_3669 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))

theorem normalization_3671 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) := (not_congr (normalization_3670 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

abbrev shared_expr_Repair040_50 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
theorem normalization_3672 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_987 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_50 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3667 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3671 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_2457 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_987 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_965 ((r1_mode) ≤ (4 : Int)) ((r1_mode) ≤ (3 : Int)) (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3672 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair040_51 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (4 : Int)) ∧ (formula_944 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
abbrev formula_988 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair040_51 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_966 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_52 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
theorem normalization_3673 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_988 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair040_52 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3387 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_3671 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_2458 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_988 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_966 ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair040_45 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ((¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair040_46 c0_depth c0_kind c0_node c0_sign r1_group r1_level))))
  have n0 : (shared_expr_Repair040_48 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3668 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (replay_2456 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Repair040_50 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3672 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (replay_2457 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3673 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) hn

theorem normalized_967 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3674 (r1_mode : Int) : (r1_mode ≤ (5 : Int)) ↔ ((r1_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_3675 (r1_mode : Int) : (r1_mode ≥ (5 : Int)) ↔ (¬ ((r1_mode) ≤ (4 : Int))) := by
  omega

theorem normalization_3676 (r1_mode : Int) : ((r1_mode ≤ (5 : Int)) ∧ (r1_mode ≥ (5 : Int))) ↔ (((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) := (and_congr (normalization_3674 r1_mode) (normalization_3675 r1_mode))

theorem normalization_3677 (r1_mode : Int) : ((r1_mode = (5 : Int)) ↔ ((r1_mode ≤ (5 : Int)) ∧ (r1_mode ≥ (5 : Int)))) ↔ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ↔ (((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int))))) := (iff_congr (normalization_3249 r1_mode) (normalization_3676 r1_mode))

-- Checked replay of rewrite.
theorem replay_2459 (r1_mode : Int) : ((r1_mode = (5 : Int)) ↔ ((r1_mode ≤ (5 : Int)) ∧ (r1_mode ≥ (5 : Int)))) := by
  classical
  have ht := (normalized_967 (((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3677 r1_mode) hn

theorem normalized_968 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3678 (r1_mode : Int) : (¬ (r1_mode ≤ (5 : Int))) ↔ (¬ ((r1_mode) ≤ (5 : Int))) := (not_congr (normalization_3674 r1_mode))

theorem normalization_3679 (r1_mode : Int) : (¬ (r1_mode ≥ (5 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (4 : Int)))) := (not_congr (normalization_3675 r1_mode))

theorem normalization_3680 (r1_mode : Int) : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int)))) ↔ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int))))) := (or_congr (normalization_3678 r1_mode) (normalization_3679 r1_mode))

theorem normalization_3681 (r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))))) ↔ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int)))))) := (not_congr (normalization_3680 r1_mode))

theorem normalization_3682 (r1_mode : Int) : (((r1_mode ≤ (5 : Int)) ∧ (r1_mode ≥ (5 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int)))))) ↔ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int))))))) := (iff_congr (normalization_3676 r1_mode) (normalization_3681 r1_mode))

-- Checked replay of rewrite.
theorem replay_2460 (r1_mode : Int) : (((r1_mode ≤ (5 : Int)) ∧ (r1_mode ≥ (5 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int)))))) := by
  classical
  have ht := (normalized_968 ((r1_mode) ≤ (5 : Int)) ((r1_mode) ≤ (4 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3682 r1_mode) hn

theorem normalized_969 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3683 (r1_mode : Int) : ((r1_mode = (5 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int)))))) ↔ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int))))))) := (iff_congr (normalization_3249 r1_mode) (normalization_3681 r1_mode))

-- Checked replay of trans.
theorem replay_2461 (r1_mode : Int) : ((r1_mode = (5 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int)))))) := by
  classical
  have ht := (normalized_969 (((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int))))))))
  have n0 : ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ↔ (((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int))))) := by
    exact Iff.mp (normalization_3677 r1_mode) (replay_2459 r1_mode)
  have n1 : ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int))))))) := by
    exact Iff.mp (normalization_3682 r1_mode) (replay_2460 r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3683 r1_mode) hn

abbrev shared_expr_Repair040_53 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ∧ ((c0_node % (2 : Int)) ≥ (1 : Int)))
abbrev formula_989 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := (shared_expr_Repair040_53 c0_depth c0_kind c0_node c0_sign r1_level)

theorem normalized_970 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ p7)) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ p7))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_54 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
theorem normalization_3684 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_989 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_54 c0_depth c0_kind c0_node c0_sign r1_level) := (and_congr (normalization_3495 c0_kind) (and_congr (normalization_3579 c0_depth r1_level) (and_congr (normalization_496 c0_sign) (normalization_524 c0_node))))

abbrev shared_expr_Repair040_55 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
theorem normalization_3685 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int))) ↔ (formula_989 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ ((shared_expr_Repair040_55 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_54 c0_depth c0_kind c0_node c0_sign r1_level)) := (iff_congr (normalization_3324 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3684 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of monotonicity.
theorem replay_2462 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int))) ↔ (formula_989 c0_depth c0_kind c0_node c0_sign r1_level)) := by
  classical
  have ht := (normalized_970 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))) (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have n0 : ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3497 c0_kind) (replay_2377 c0_kind)
  have n1 : (shared_expr_Repair040_3 c0_depth r1_level) := by
    exact Iff.mp (normalization_3582 c0_depth r1_level) (replay_2413 c0_depth r1_level)
  have n2 : (shared_expr_Repair040_39 c0_sign) := by
    exact Iff.mp (normalization_3537 c0_sign) (replay_2394 c0_sign)
  have n3 : (shared_expr_Repair040_21 c0_node) := by
    exact Iff.mp (normalization_3628 c0_node) (replay_2437 c0_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_3685 c0_depth c0_kind c0_node c0_sign r1_level) hn

theorem normalized_971 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ p5) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_56 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_3686 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_887 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level) := (or_congr (normalization_453 c0_kind) (or_congr (normalization_455 c0_kind) (or_congr (normalization_497 c0_sign) (or_congr (normalization_525 c0_node) (or_congr (normalization_3576 c0_depth r1_level) (normalization_3577 c0_depth r1_level))))))

theorem normalization_3687 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (¬ (formula_887 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ (¬ (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level)) := (not_congr (normalization_3686 c0_depth c0_kind c0_node c0_sign r1_level))

theorem normalization_3688 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : ((formula_989 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (formula_887 c0_depth c0_kind c0_node c0_sign r1_level))) ↔ ((shared_expr_Repair040_54 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level))) := (iff_congr (normalization_3684 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3687 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of rewrite.
theorem replay_2463 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : ((formula_989 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (formula_887 c0_depth c0_kind c0_node c0_sign r1_level))) := by
  classical
  have ht := (normalized_971 ((c0_kind) ≤ (1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3688 c0_depth c0_kind c0_node c0_sign r1_level) hn

theorem normalized_972 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3689 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int))) ↔ (¬ (formula_887 c0_depth c0_kind c0_node c0_sign r1_level))) ↔ ((shared_expr_Repair040_55 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level))) := (iff_congr (normalization_3324 c0_depth c0_kind c0_node c0_sign r1_level) (normalization_3687 c0_depth c0_kind c0_node c0_sign r1_level))

-- Checked replay of trans.
theorem replay_2464 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ (c0_depth = r1_level) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ∧ ((c0_node % (2 : Int)) = (1 : Int))) ↔ (¬ (formula_887 c0_depth c0_kind c0_node c0_sign r1_level))) := by
  classical
  have ht := (normalized_972 (shared_expr_Repair040_55 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_54 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level))
  have n0 : ((shared_expr_Repair040_55 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Repair040_54 c0_depth c0_kind c0_node c0_sign r1_level)) := by
    exact Iff.mp (normalization_3685 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2462 c0_depth c0_kind c0_node c0_sign r1_level)
  have n1 : ((shared_expr_Repair040_54 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level))) := by
    exact Iff.mp (normalization_3688 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2463 c0_depth c0_kind c0_node c0_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3689 c0_depth c0_kind c0_node c0_sign r1_level) hn

abbrev shared_expr_Repair040_57 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_887 c0_depth c0_kind c0_node c0_sign r1_level))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_879 c0_depth c0_kind c0_sign r1_level))))
abbrev formula_990 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair040_57 c0_depth c0_kind c0_node c0_sign r1_group r1_level)

theorem normalized_973 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_58 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))))
theorem normalization_3690 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_990 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_58 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_3687 c0_depth c0_kind c0_node c0_sign r1_level)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_3541 c0_depth c0_kind c0_sign r1_level)))

abbrev shared_expr_Repair040_59 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair040_55 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair040_44 c0_depth c0_kind c0_sign r1_level)))
theorem normalization_3691 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_945 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_990 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_59 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_58 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3388 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3690 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_2465 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_945 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_990 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_973 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair040_55 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_44 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((shared_expr_Repair040_55 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level))) := by
    exact Iff.mp (normalization_3689 c0_depth c0_kind c0_node c0_sign r1_level) (replay_2464 c0_depth c0_kind c0_node c0_sign r1_level)
  have n2 : ((shared_expr_Repair040_44 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))) := by
    exact Iff.mp (normalization_3543 c0_depth c0_kind c0_sign r1_level) (replay_2397 c0_depth c0_kind c0_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3691 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

theorem normalized_974 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair040_60 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level))))
theorem normalization_3692 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_60 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_3541 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_3687 c0_depth c0_kind c0_node c0_sign r1_level)))

theorem normalization_3693 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_990 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_58 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_60 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3690 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3692 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_2466 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_990 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_974 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair040_56 c0_depth c0_kind c0_node c0_sign r1_level) (shared_expr_Repair040_42 c0_depth c0_kind c0_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3693 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

theorem normalized_975 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3694 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_945 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair040_59 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_60 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (iff_congr (normalization_3388 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (normalization_3692 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_2467 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : ((formula_945 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_975 (shared_expr_Repair040_59 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_58 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (shared_expr_Repair040_60 c0_depth c0_kind c0_node c0_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair040_59 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_58 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3691 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2465 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair040_58 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Repair040_60 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3693 c0_depth c0_kind c0_node c0_sign r1_group r1_level) (replay_2466 c0_depth c0_kind c0_node c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3694 c0_depth c0_kind c0_node c0_sign r1_group r1_level) hn

end H4Formal.Generated.Repair
