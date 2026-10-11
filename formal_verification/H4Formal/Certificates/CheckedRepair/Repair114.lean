import H4Formal.Certificates.CheckedRepair.Repair113

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair114_0 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))))
abbrev formula_2840 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair114_0 c3_depth c3_kind c3_sign r1_group r1_level)

theorem normalized_2431 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_1 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
abbrev shared_expr_Repair114_2 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))))
theorem normalization_8089 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2840 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_2 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_6942 c3_kind)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_8086 c3_depth c3_kind c3_sign r1_level)))

abbrev shared_expr_Repair114_3 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair114_4 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_8090 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2816 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2840 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_2 c3_depth c3_kind c3_sign r1_group r1_level)) := (iff_congr (normalization_7967 c3_depth c3_kind c3_sign r1_group r1_level) (normalization_8089 c3_depth c3_kind c3_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_7659 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2816 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2840 c3_depth c3_kind c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2431 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) (shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6944 c3_kind) (replay_6119 c3_kind)
  have n2 : ((shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))) := by
    exact Iff.mp (normalization_8088 c3_depth c3_kind c3_sign r1_level) (replay_7658 c3_depth c3_kind c3_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8090 c3_depth c3_kind c3_sign r1_group r1_level) hn

theorem normalized_2432 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_5 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
theorem normalization_8091 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_8086 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_6942 c3_kind)))

theorem normalization_8092 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2840 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_2 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)) := (iff_congr (normalization_8089 c3_depth c3_kind c3_sign r1_group r1_level) (normalization_8091 c3_depth c3_kind c3_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_7660 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2840 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2432 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_8092 c3_depth c3_kind c3_sign r1_group r1_level) hn

theorem normalized_2433 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8093 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2816 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)) := (iff_congr (normalization_7967 c3_depth c3_kind c3_sign r1_group r1_level) (normalization_8091 c3_depth c3_kind c3_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_7661 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2816 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2433 (shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level) (shared_expr_Repair114_2 c3_depth c3_kind c3_sign r1_group r1_level) (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_2 c3_depth c3_kind c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8090 c3_depth c3_kind c3_sign r1_group r1_level) (replay_7659 c3_depth c3_kind c3_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair114_2 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8092 c3_depth c3_kind c3_sign r1_group r1_level) (replay_7660 c3_depth c3_kind c3_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8093 c3_depth c3_kind c3_sign r1_group r1_level) hn

abbrev shared_expr_Repair114_6 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (0 : Int)) ∧ (formula_2816 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))))) ∧ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)))
abbrev formula_2841 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_6 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)

theorem normalized_2434 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8094 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))))) ∧ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)) := (and_congr (normalization_3485 r1_mode) (normalization_8091 c3_depth c3_kind c3_sign r1_group r1_level))

abbrev shared_expr_Repair114_7 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)))
theorem normalization_8095 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2841 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_7 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_7968 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (normalization_8094 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_7662 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2841 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2434 (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))) (shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level) (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3487 r1_mode) (replay_2371 r1_mode)
  have n1 : ((shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8093 c3_depth c3_kind c3_sign r1_group r1_level) (replay_7661 c3_depth c3_kind c3_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8095 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair114_8 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))))) ∧ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)))))
abbrev formula_2842 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_8 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)

theorem normalized_2435 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ (¬ p1)) ∨ (¬ p0) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8096 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)) := (not_congr (normalization_8091 c3_depth c3_kind c3_sign r1_group r1_level))

theorem normalization_8097 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level))) ↔ ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level))) := (or_congr (normalization_2807 r1_mode) (or_congr (normalization_2809 r1_mode) (normalization_8096 c3_depth c3_kind c3_sign r1_group r1_level)))

theorem normalization_8098 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)))) ↔ (¬ ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)))) := (not_congr (normalization_8097 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

abbrev shared_expr_Repair114_9 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)))))
theorem normalization_8099 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2842 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_9 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_8094 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (normalization_8098 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_7663 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2842 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2435 ((r1_mode) ≤ (0 : Int)) ((r1_mode) ≤ (-1 : Int)) (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level))
  have hn := ht
  exact Iff.mpr (normalization_8099 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair114_10 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (0 : Int)) ∧ (formula_2816 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)))))
abbrev formula_2843 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_10 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)

theorem normalized_2436 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_11 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)))))
theorem normalization_8100 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2843 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_11 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_7968 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (normalization_8098 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_7664 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2843 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2436 ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair114_4 c3_depth c3_kind c3_sign r1_group r1_level)) ((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level)) ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair114_5 c3_depth c3_kind c3_sign r1_group r1_level))))
  have n0 : (shared_expr_Repair114_7 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_8095 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (replay_7662 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Repair114_9 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_8099 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (replay_7663 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8100 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) hn

theorem normalized_2437 (p0 p1 p2 : Prop) : (((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p0))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p0)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_12 (c3_sign : Int) : Prop := (((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
theorem normalization_8101 (c3_sign : Int) : (((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))) ↔ ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ↔ (shared_expr_Repair114_12 c3_sign) := (iff_congr (normalization_7106 c3_sign) (normalization_7571 c3_sign))

-- Checked replay of rewrite.
theorem replay_7665 (c3_sign : Int) : (((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int))) ↔ ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_2437 ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8101 c3_sign) hn

abbrev shared_expr_Repair114_13 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ∧ ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))))
abbrev formula_2844 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := (shared_expr_Repair114_13 c3_depth c3_kind c3_sign r1_level)

theorem normalized_2438 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → ((p0 ∧ p2 ∧ p4) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_14 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
theorem normalization_8102 (c3_depth c3_kind c3_sign r1_level : Int) : (formula_2844 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Repair114_14 c3_depth c3_kind c3_sign r1_level) := (and_congr (normalization_6932 c3_kind) (and_congr (normalization_8079 c3_depth r1_level) (normalization_7571 c3_sign)))

abbrev shared_expr_Repair114_15 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
theorem normalization_8103 (c3_depth c3_kind c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (formula_2844 c3_depth c3_kind c3_sign r1_level)) ↔ ((shared_expr_Repair114_15 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Repair114_14 c3_depth c3_kind c3_sign r1_level)) := (iff_congr (normalization_7969 c3_depth c3_kind c3_sign r1_level) (normalization_8102 c3_depth c3_kind c3_sign r1_level))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair114_16 (c3_depth r1_level : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))))
theorem replay_7666 (c3_depth c3_kind c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (formula_2844 c3_depth c3_kind c3_sign r1_level)) := by
  classical
  have ht := (normalized_2438 (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
  have n0 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6934 c3_kind) (replay_6116 c3_kind)
  have n1 : (shared_expr_Repair114_16 c3_depth r1_level) := by
    exact Iff.mp (normalization_8081 c3_depth r1_level) (replay_7654 c3_depth r1_level)
  have n2 : (shared_expr_Repair114_12 c3_sign) := by
    exact Iff.mp (normalization_8101 c3_sign) (replay_7665 c3_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8103 c3_depth c3_kind c3_sign r1_level) hn

theorem normalized_2439 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ (¬ p2)) ∨ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_17 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_8104 (c3_depth c3_kind c3_sign r1_level : Int) : (formula_2592 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7572 c3_sign) (or_congr (normalization_8076 c3_depth r1_level) (normalization_8077 c3_depth r1_level)))))

theorem normalization_8105 (c3_depth c3_kind c3_sign r1_level : Int) : (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level)) ↔ (¬ (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level)) := (not_congr (normalization_8104 c3_depth c3_kind c3_sign r1_level))

theorem normalization_8106 (c3_depth c3_kind c3_sign r1_level : Int) : ((formula_2844 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level))) ↔ ((shared_expr_Repair114_14 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))) := (iff_congr (normalization_8102 c3_depth c3_kind c3_sign r1_level) (normalization_8105 c3_depth c3_kind c3_sign r1_level))

-- Checked replay of rewrite.
theorem replay_7667 (c3_depth c3_kind c3_sign r1_level : Int) : ((formula_2844 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level))) := by
  classical
  have ht := (normalized_2439 ((c3_kind) ≤ (1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
  have hn := ht
  exact Iff.mpr (normalization_8106 c3_depth c3_kind c3_sign r1_level) hn

theorem normalized_2440 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8107 (c3_depth c3_kind c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level))) ↔ ((shared_expr_Repair114_15 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))) := (iff_congr (normalization_7969 c3_depth c3_kind c3_sign r1_level) (normalization_8105 c3_depth c3_kind c3_sign r1_level))

-- Checked replay of trans.
theorem replay_7668 (c3_depth c3_kind c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) = (1 : Int)) ∧ ((c3_sign = (1 : Int)) ∨ (c3_sign = (2 : Int)))) ↔ (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level))) := by
  classical
  have ht := (normalized_2440 (shared_expr_Repair114_15 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_14 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))
  have n0 : ((shared_expr_Repair114_15 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Repair114_14 c3_depth c3_kind c3_sign r1_level)) := by
    exact Iff.mp (normalization_8103 c3_depth c3_kind c3_sign r1_level) (replay_7666 c3_depth c3_kind c3_sign r1_level)
  have n1 : ((shared_expr_Repair114_14 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))) := by
    exact Iff.mp (normalization_8106 c3_depth c3_kind c3_sign r1_level) (replay_7667 c3_depth c3_kind c3_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8107 c3_depth c3_kind c3_sign r1_level) hn

abbrev shared_expr_Repair114_18 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level))))
abbrev formula_2845 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair114_18 c3_depth c3_kind c3_sign r1_group r1_level)

theorem normalized_2441 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_19 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))))
theorem normalization_8108 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2845 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_19 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_6942 c3_kind)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_8105 c3_depth c3_kind c3_sign r1_level)))

abbrev shared_expr_Repair114_20 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair114_15 c3_depth c3_kind c3_sign r1_level)))
theorem normalization_8109 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2817 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2845 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_19 c3_depth c3_kind c3_sign r1_group r1_level)) := (iff_congr (normalization_7970 c3_depth c3_kind c3_sign r1_group r1_level) (normalization_8108 c3_depth c3_kind c3_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_7669 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2817 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2845 c3_depth c3_kind c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2441 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) (shared_expr_Repair114_15 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6944 c3_kind) (replay_6119 c3_kind)
  have n2 : ((shared_expr_Repair114_15 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))) := by
    exact Iff.mp (normalization_8107 c3_depth c3_kind c3_sign r1_level) (replay_7668 c3_depth c3_kind c3_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8109 c3_depth c3_kind c3_sign r1_group r1_level) hn

theorem normalized_2442 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_21 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
theorem normalization_8110 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_8105 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_6942 c3_kind)))

theorem normalization_8111 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2845 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_19 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)) := (iff_congr (normalization_8108 c3_depth c3_kind c3_sign r1_group r1_level) (normalization_8110 c3_depth c3_kind c3_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_7670 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2845 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2442 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) (shared_expr_Repair114_17 c3_depth c3_kind c3_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_8111 c3_depth c3_kind c3_sign r1_group r1_level) hn

theorem normalized_2443 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8112 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2817 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)) := (iff_congr (normalization_7970 c3_depth c3_kind c3_sign r1_group r1_level) (normalization_8110 c3_depth c3_kind c3_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_7671 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((formula_2817 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2443 (shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level) (shared_expr_Repair114_19 c3_depth c3_kind c3_sign r1_group r1_level) (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_19 c3_depth c3_kind c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8109 c3_depth c3_kind c3_sign r1_group r1_level) (replay_7669 c3_depth c3_kind c3_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair114_19 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8111 c3_depth c3_kind c3_sign r1_group r1_level) (replay_7670 c3_depth c3_kind c3_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8112 c3_depth c3_kind c3_sign r1_group r1_level) hn

abbrev shared_expr_Repair114_22 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (1 : Int)) ∧ (formula_2817 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))))) ∧ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)))
abbrev formula_2846 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_22 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)

theorem normalized_2444 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8113 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))))) ∧ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)) := (and_congr (normalization_3534 r1_mode) (normalization_8110 c3_depth c3_kind c3_sign r1_group r1_level))

abbrev shared_expr_Repair114_23 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)))
theorem normalization_8114 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2846 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_23 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_7971 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (normalization_8113 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_7672 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2846 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2444 (((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))) (shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level) (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3536 r1_mode) (replay_2393 r1_mode)
  have n1 : ((shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8112 c3_depth c3_kind c3_sign r1_group r1_level) (replay_7671 c3_depth c3_kind c3_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8114 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair114_24 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))))) ∧ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)))))
abbrev formula_2847 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_24 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)

theorem normalized_2445 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8115 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)) := (not_congr (normalization_8110 c3_depth c3_kind c3_sign r1_group r1_level))

theorem normalization_8116 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level))) := (or_congr (normalization_3531 r1_mode) (or_congr (normalization_3532 r1_mode) (normalization_8115 c3_depth c3_kind c3_sign r1_group r1_level)))

theorem normalization_8117 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)))) := (not_congr (normalization_8116 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

abbrev shared_expr_Repair114_25 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)))))
theorem normalization_8118 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2847 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_25 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_8113 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (normalization_8117 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_7673 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2847 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2445 ((r1_mode) ≤ (1 : Int)) ((r1_mode) ≤ (0 : Int)) (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level))
  have hn := ht
  exact Iff.mpr (normalization_8118 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair114_26 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (1 : Int)) ∧ (formula_2817 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)))))
abbrev formula_2848 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_26 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)

theorem normalized_2446 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_27 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)))))
theorem normalization_8119 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2848 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_27 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_7971 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (normalization_8117 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_7674 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (formula_2848 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2446 ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair114_20 c3_depth c3_kind c3_sign r1_group r1_level)) ((¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level)) ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair114_21 c3_depth c3_kind c3_sign r1_group r1_level))))
  have n0 : (shared_expr_Repair114_23 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_8114 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (replay_7672 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Repair114_25 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_8118 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (replay_7673 c3_depth c3_kind c3_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8119 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) hn

theorem normalized_2447 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8120 (c3_depth r1_level : Int) : (c3_depth ≤ r1_level) ↔ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_8121 (c3_depth r1_level : Int) : (c3_depth ≥ r1_level) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8122 (c3_depth r1_level : Int) : ((c3_depth ≤ r1_level) ∧ (c3_depth ≥ r1_level)) ↔ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (and_congr (normalization_8120 c3_depth r1_level) (normalization_8121 c3_depth r1_level))

abbrev shared_expr_Repair114_28 (c3_depth r1_level : Int) : Prop := ((((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ↔ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_8123 (c3_depth r1_level : Int) : ((c3_depth = r1_level) ↔ ((c3_depth ≤ r1_level) ∧ (c3_depth ≥ r1_level))) ↔ (shared_expr_Repair114_28 c3_depth r1_level) := (iff_congr (normalization_7835 c3_depth r1_level) (normalization_8122 c3_depth r1_level))

-- Checked replay of rewrite.
theorem replay_7675 (c3_depth r1_level : Int) : ((c3_depth = r1_level) ↔ ((c3_depth ≤ r1_level) ∧ (c3_depth ≥ r1_level))) := by
  classical
  have ht := (normalized_2447 (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8123 c3_depth r1_level) hn

theorem normalized_2448 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8124 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_8125 (c3_depth r1_level : Int) : ((c3_depth ≤ r1_level) ↔ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (iff_congr (normalization_8120 c3_depth r1_level) (normalization_8124 c3_depth r1_level))

-- Checked replay of rewrite.
theorem replay_7676 (c3_depth r1_level : Int) : ((c3_depth ≤ r1_level) ↔ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2448 ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8125 c3_depth r1_level) hn

theorem normalized_2449 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8126 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8127 (c3_depth r1_level : Int) : ((c3_depth ≥ r1_level) ↔ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_8121 c3_depth r1_level) (normalization_8126 c3_depth r1_level))

-- Checked replay of rewrite.
theorem replay_7677 (c3_depth r1_level : Int) : ((c3_depth ≥ r1_level) ↔ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2449 ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8127 c3_depth r1_level) hn

theorem normalized_2450 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8128 (c3_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (and_congr (normalization_8124 c3_depth r1_level) (normalization_8126 c3_depth r1_level))

theorem normalization_8129 (c3_depth r1_level : Int) : (((c3_depth ≤ r1_level) ∧ (c3_depth ≥ r1_level)) ↔ (((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (shared_expr_Repair114_28 c3_depth r1_level) := (iff_congr (normalization_8122 c3_depth r1_level) (normalization_8128 c3_depth r1_level))

-- Checked replay of monotonicity.
theorem replay_7678 (c3_depth r1_level : Int) : (((c3_depth ≤ r1_level) ∧ (c3_depth ≥ r1_level)) ↔ (((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := by
  classical
  have ht := (normalized_2450 ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
  have n0 : (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8125 c3_depth r1_level) (replay_7676 c3_depth r1_level)
  have n1 : ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8127 c3_depth r1_level) (replay_7677 c3_depth r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8129 c3_depth r1_level) hn

abbrev shared_expr_Repair114_29 (c3_depth r1_level : Int) : Prop := ((((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
abbrev formula_2849 (c3_depth r1_level : Int) : Prop := (shared_expr_Repair114_29 c3_depth r1_level)

theorem normalized_2451 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8130 (c3_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_8124 c3_depth r1_level))

theorem normalization_8131 (c3_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_8126 c3_depth r1_level))

theorem normalization_8132 (c3_depth r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) := (or_congr (normalization_8130 c3_depth r1_level) (normalization_8131 c3_depth r1_level))

theorem normalization_8133 (c3_depth r1_level : Int) : (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) := (not_congr (normalization_8132 c3_depth r1_level))

abbrev shared_expr_Repair114_30 (c3_depth r1_level : Int) : Prop := ((((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))))
theorem normalization_8134 (c3_depth r1_level : Int) : (formula_2849 c3_depth r1_level) ↔ (shared_expr_Repair114_30 c3_depth r1_level) := (iff_congr (normalization_8128 c3_depth r1_level) (normalization_8133 c3_depth r1_level))

-- Checked replay of rewrite.
theorem replay_7679 (c3_depth r1_level : Int) : (formula_2849 c3_depth r1_level) := by
  classical
  have ht := (normalized_2451 ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8134 c3_depth r1_level) hn

theorem normalized_2452 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8135 (c3_depth r1_level : Int) : (((c3_depth ≤ r1_level) ∧ (c3_depth ≥ r1_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Repair114_30 c3_depth r1_level) := (iff_congr (normalization_8122 c3_depth r1_level) (normalization_8133 c3_depth r1_level))

-- Checked replay of trans.
theorem replay_7680 (c3_depth r1_level : Int) : (((c3_depth ≤ r1_level) ∧ (c3_depth ≥ r1_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_2452 (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) (shared_expr_Repair114_30 c3_depth r1_level))
  have n0 : (shared_expr_Repair114_28 c3_depth r1_level) := by
    exact Iff.mp (normalization_8129 c3_depth r1_level) (replay_7678 c3_depth r1_level)
  have n1 : (shared_expr_Repair114_30 c3_depth r1_level) := by
    exact Iff.mp (normalization_8134 c3_depth r1_level) (replay_7679 c3_depth r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8135 c3_depth r1_level) hn

theorem normalized_2453 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8136 (c3_depth r1_level : Int) : ((c3_depth = r1_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Repair114_30 c3_depth r1_level) := (iff_congr (normalization_7835 c3_depth r1_level) (normalization_8133 c3_depth r1_level))

-- Checked replay of trans.
theorem replay_7681 (c3_depth r1_level : Int) : ((c3_depth = r1_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_2453 (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) (shared_expr_Repair114_30 c3_depth r1_level))
  have n0 : (shared_expr_Repair114_28 c3_depth r1_level) := by
    exact Iff.mp (normalization_8123 c3_depth r1_level) (replay_7675 c3_depth r1_level)
  have n1 : (shared_expr_Repair114_30 c3_depth r1_level) := by
    exact Iff.mp (normalization_8135 c3_depth r1_level) (replay_7680 c3_depth r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8136 c3_depth r1_level) hn

theorem normalized_2454 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8137 (c3_node : Int) : ((c3_node % (2 : Int)) ≥ (0 : Int)) ↔ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_8138 (c3_node : Int) : (((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (and_congr (normalization_7579 c3_node) (normalization_8137 c3_node))

abbrev shared_expr_Repair114_31 (c3_node : Int) : Prop := (((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
theorem normalization_8139 (c3_node : Int) : (((c3_node % (2 : Int)) = (0 : Int)) ↔ (((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (0 : Int)))) ↔ (shared_expr_Repair114_31 c3_node) := (iff_congr (normalization_7112 c3_node) (normalization_8138 c3_node))

-- Checked replay of rewrite.
theorem replay_7682 (c3_node : Int) : (((c3_node % (2 : Int)) = (0 : Int)) ↔ (((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2454 ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8139 c3_node) hn

-- Checked replay of rewrite.
theorem replay_7683 (c3_node : Int) : (((c3_node % (2 : Int)) ≥ (0 : Int)) ↔ True) := by
  classical
  first | omega | grind (splits := 40)

theorem normalized_2455 (p0 p1 : Prop) : (((p0 ↔ True)) → (((¬ p1) ∧ p0) ↔ ((¬ p1) ∧ True))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8140 (c3_node : Int) : (((c3_node % (2 : Int)) ≥ (0 : Int)) ↔ True) ↔ (((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ True) := (iff_congr (normalization_8137 c3_node) (normalization_305))

theorem normalization_8141 (c3_node : Int) : (((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ True) := (and_congr (normalization_7579 c3_node) (normalization_305))

abbrev shared_expr_Repair114_32 (c3_node : Int) : Prop := (((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ True))
theorem normalization_8142 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (0 : Int))) ↔ (((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ True)) ↔ (shared_expr_Repair114_32 c3_node) := (iff_congr (normalization_8138 c3_node) (normalization_8141 c3_node))

-- Checked replay of monotonicity.
theorem replay_7684 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (0 : Int))) ↔ (((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ True)) := by
  classical
  have ht := (normalized_2455 ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ True) := by
    exact Iff.mp (normalization_8140 c3_node) (replay_7683 c3_node)
  have hn := ht n0
  exact Iff.mpr (normalization_8142 c3_node) hn

theorem normalized_2456 (p0 : Prop) : (((¬ p0) ∧ True) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8143 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((c3_node % (2 : Int)) ≤ (0 : Int))) ↔ (((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ True) ↔ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_8141 c3_node) (normalization_7579 c3_node))

-- Checked replay of rewrite.
theorem replay_7685 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((c3_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2456 ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8143 c3_node) hn

theorem normalized_2457 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_33 (c3_node : Int) : Prop := (((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
theorem normalization_8144 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (0 : Int))) ↔ ((c3_node % (2 : Int)) ≤ (0 : Int))) ↔ (shared_expr_Repair114_33 c3_node) := (iff_congr (normalization_8138 c3_node) (normalization_7579 c3_node))

-- Checked replay of trans.
theorem replay_7686 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (0 : Int))) ↔ ((c3_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2457 ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ True) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair114_32 c3_node) := by
    exact Iff.mp (normalization_8142 c3_node) (replay_7684 c3_node)
  have n1 : (((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ True) ↔ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8143 c3_node) (replay_7685 c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8144 c3_node) hn

theorem normalized_2458 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8145 (c3_node : Int) : (((c3_node % (2 : Int)) = (0 : Int)) ↔ ((c3_node % (2 : Int)) ≤ (0 : Int))) ↔ (shared_expr_Repair114_33 c3_node) := (iff_congr (normalization_7112 c3_node) (normalization_7579 c3_node))

-- Checked replay of trans.
theorem replay_7687 (c3_node : Int) : (((c3_node % (2 : Int)) = (0 : Int)) ↔ ((c3_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2458 ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) (shared_expr_Repair114_33 c3_node))
  have n0 : (shared_expr_Repair114_31 c3_node) := by
    exact Iff.mp (normalization_8139 c3_node) (replay_7682 c3_node)
  have n1 : (shared_expr_Repair114_33 c3_node) := by
    exact Iff.mp (normalization_8144 c3_node) (replay_7686 c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8145 c3_node) hn

abbrev shared_expr_Repair114_34 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ∧ ((c3_node % (2 : Int)) ≤ (0 : Int)))
abbrev formula_2850 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := (shared_expr_Repair114_34 c3_depth c3_kind c3_node c3_sign r1_level)

theorem normalized_2459 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ (¬ p7))) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ (¬ p7)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_35 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) ∧ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
theorem normalization_8146 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (formula_2850 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Repair114_35 c3_depth c3_kind c3_node c3_sign r1_level) := (and_congr (normalization_6932 c3_kind) (and_congr (normalization_8133 c3_depth r1_level) (and_congr (normalization_7559 c3_sign) (normalization_7579 c3_node))))

abbrev shared_expr_Repair114_36 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
theorem normalization_8147 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int))) ↔ (formula_2850 c3_depth c3_kind c3_node c3_sign r1_level)) ↔ ((shared_expr_Repair114_36 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Repair114_35 c3_depth c3_kind c3_node c3_sign r1_level)) := (iff_congr (normalization_7907 c3_depth c3_kind c3_node c3_sign r1_level) (normalization_8146 c3_depth c3_kind c3_node c3_sign r1_level))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair114_37 (c3_sign : Int) : Prop := (((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
theorem replay_7688 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int))) ↔ (formula_2850 c3_depth c3_kind c3_node c3_sign r1_level)) := by
  classical
  have ht := (normalized_2459 (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6934 c3_kind) (replay_6116 c3_kind)
  have n1 : (shared_expr_Repair114_30 c3_depth r1_level) := by
    exact Iff.mp (normalization_8136 c3_depth r1_level) (replay_7681 c3_depth r1_level)
  have n2 : (shared_expr_Repair114_37 c3_sign) := by
    exact Iff.mp (normalization_8082 c3_sign) (replay_7655 c3_sign)
  have n3 : (shared_expr_Repair114_33 c3_node) := by
    exact Iff.mp (normalization_8145 c3_node) (replay_7687 c3_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_8147 c3_depth c3_kind c3_node c3_sign r1_level) hn

theorem normalized_2460 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ (¬ p5)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_38 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_8148 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (formula_2594 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7560 c3_sign) (or_congr (normalization_7580 c3_node) (or_congr (normalization_8130 c3_depth r1_level) (normalization_8131 c3_depth r1_level))))))

theorem normalization_8149 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (¬ (formula_2594 c3_depth c3_kind c3_node c3_sign r1_level)) ↔ (¬ (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level)) := (not_congr (normalization_8148 c3_depth c3_kind c3_node c3_sign r1_level))

theorem normalization_8150 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : ((formula_2850 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (formula_2594 c3_depth c3_kind c3_node c3_sign r1_level))) ↔ ((shared_expr_Repair114_35 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))) := (iff_congr (normalization_8146 c3_depth c3_kind c3_node c3_sign r1_level) (normalization_8149 c3_depth c3_kind c3_node c3_sign r1_level))

-- Checked replay of rewrite.
theorem replay_7689 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : ((formula_2850 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (formula_2594 c3_depth c3_kind c3_node c3_sign r1_level))) := by
  classical
  have ht := (normalized_2460 ((c3_kind) ≤ (1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8150 c3_depth c3_kind c3_node c3_sign r1_level) hn

theorem normalized_2461 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_39 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := (((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (0 : Int))) ↔ (¬ (formula_2594 c3_depth c3_kind c3_node c3_sign r1_level)))
theorem normalization_8151 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (shared_expr_Repair114_39 c3_depth c3_kind c3_node c3_sign r1_level) ↔ ((shared_expr_Repair114_36 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))) := (iff_congr (normalization_7907 c3_depth c3_kind c3_node c3_sign r1_level) (normalization_8149 c3_depth c3_kind c3_node c3_sign r1_level))

-- Checked replay of trans.
theorem replay_7690 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (shared_expr_Repair114_39 c3_depth c3_kind c3_node c3_sign r1_level) := by
  classical
  have ht := (normalized_2461 (shared_expr_Repair114_36 c3_depth c3_kind c3_node c3_sign r1_level) (shared_expr_Repair114_35 c3_depth c3_kind c3_node c3_sign r1_level) (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))
  have n0 : ((shared_expr_Repair114_36 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Repair114_35 c3_depth c3_kind c3_node c3_sign r1_level)) := by
    exact Iff.mp (normalization_8147 c3_depth c3_kind c3_node c3_sign r1_level) (replay_7688 c3_depth c3_kind c3_node c3_sign r1_level)
  have n1 : ((shared_expr_Repair114_35 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))) := by
    exact Iff.mp (normalization_8150 c3_depth c3_kind c3_node c3_sign r1_level) (replay_7689 c3_depth c3_kind c3_node c3_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8151 c3_depth c3_kind c3_node c3_sign r1_level) hn

abbrev shared_expr_Repair114_40 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_2594 c3_depth c3_kind c3_node c3_sign r1_level))))
abbrev formula_2851 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair114_40 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

theorem normalized_2462 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_41 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))))
theorem normalization_8152 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2851 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_41 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_8086 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_8149 c3_depth c3_kind c3_node c3_sign r1_level)))

abbrev shared_expr_Repair114_42 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair114_36 c3_depth c3_kind c3_node c3_sign r1_level)))
theorem normalization_8153 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2851 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_41 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (iff_congr (normalization_7972 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (normalization_8152 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_7691 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2851 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2462 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_36 c3_depth c3_kind c3_node c3_sign r1_level) (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))) := by
    exact Iff.mp (normalization_8088 c3_depth c3_kind c3_sign r1_level) (replay_7658 c3_depth c3_kind c3_sign r1_level)
  have n2 : ((shared_expr_Repair114_36 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))) := by
    exact Iff.mp (normalization_8151 c3_depth c3_kind c3_node c3_sign r1_level) (replay_7690 c3_depth c3_kind c3_node c3_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8153 c3_depth c3_kind c3_node c3_sign r1_group r1_level) hn

theorem normalized_2463 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_43 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))))
theorem normalization_8154 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_8149 c3_depth c3_kind c3_node c3_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_8086 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_8155 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2851 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_41 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (iff_congr (normalization_8152 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (normalization_8154 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_7692 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2851 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2463 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_38 c3_depth c3_kind c3_node c3_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_8155 c3_depth c3_kind c3_node c3_sign r1_group r1_level) hn

theorem normalized_2464 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8156 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (iff_congr (normalization_7972 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (normalization_8154 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_7693 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2464 (shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (shared_expr_Repair114_41 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_41 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8153 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (replay_7691 c3_depth c3_kind c3_node c3_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair114_41 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8155 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (replay_7692 c3_depth c3_kind c3_node c3_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8156 c3_depth c3_kind c3_node c3_sign r1_group r1_level) hn

abbrev shared_expr_Repair114_44 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (2 : Int)) ∧ (formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))))) ∧ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
abbrev formula_2852 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_44 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

theorem normalized_2465 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8157 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))))) ∧ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_3563 r1_mode) (normalization_8154 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Repair114_45 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
theorem normalization_8158 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2852 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_45 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_7973 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (normalization_8157 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_7694 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2852 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2465 (((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))) (shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3565 r1_mode) (replay_2406 r1_mode)
  have n1 : ((shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8156 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (replay_7693 c3_depth c3_kind c3_node c3_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8158 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair114_46 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))))) ∧ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))))
abbrev formula_2853 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_46 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

theorem normalized_2466 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8159 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (not_congr (normalization_8154 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

theorem normalization_8160 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := (or_congr (normalization_3560 r1_mode) (or_congr (normalization_3561 r1_mode) (normalization_8159 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))

theorem normalization_8161 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) := (not_congr (normalization_8160 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

abbrev shared_expr_Repair114_47 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))))
theorem normalization_8162 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2853 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_47 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_8157 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (normalization_8161 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_7695 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2853 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2466 ((r1_mode) ≤ (2 : Int)) ((r1_mode) ≤ (1 : Int)) (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level))
  have hn := ht
  exact Iff.mpr (normalization_8162 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair114_48 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (2 : Int)) ∧ (formula_2818 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))))
abbrev formula_2854 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_48 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

theorem normalized_2467 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_49 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))))
theorem normalization_8163 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2854 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_49 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_7973 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (normalization_8161 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_7696 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2854 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2467 ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair114_42 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ((¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) ∧ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair114_43 c3_depth c3_kind c3_node c3_sign r1_group r1_level))))
  have n0 : (shared_expr_Repair114_45 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_8158 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (replay_7694 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Repair114_47 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_8162 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (replay_7695 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8163 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) hn

theorem normalized_2468 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8164 (c3_node : Int) : ((c3_node % (2 : Int)) ≤ (1 : Int)) ↔ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) := by
  omega

theorem normalization_8165 (c3_node : Int) : (((c3_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := (and_congr (normalization_8164 c3_node) (normalization_7591 c3_node))

abbrev shared_expr_Repair114_50 (c3_node : Int) : Prop := (((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
theorem normalization_8166 (c3_node : Int) : (((c3_node % (2 : Int)) = (1 : Int)) ↔ (((c3_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (1 : Int)))) ↔ (shared_expr_Repair114_50 c3_node) := (iff_congr (normalization_7116 c3_node) (normalization_8165 c3_node))

-- Checked replay of rewrite.
theorem replay_7697 (c3_node : Int) : (((c3_node % (2 : Int)) = (1 : Int)) ↔ (((c3_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2468 ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8166 c3_node) hn

-- Checked replay of rewrite.
theorem replay_7698 (c3_node : Int) : (((c3_node % (2 : Int)) ≤ (1 : Int)) ↔ True) := by
  classical
  first | omega | grind (splits := 40)

theorem normalized_2469 (p0 p1 : Prop) : ((((¬ p0) ↔ True)) → (((¬ p0) ∧ p1) ↔ (True ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8167 (c3_node : Int) : (((c3_node % (2 : Int)) ≤ (1 : Int)) ↔ True) ↔ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ↔ True) := (iff_congr (normalization_8164 c3_node) (normalization_305))

theorem normalization_8168 (c3_node : Int) : (True ∧ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := (and_congr (normalization_305) (normalization_7591 c3_node))

abbrev shared_expr_Repair114_51 (c3_node : Int) : Prop := (((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (True ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
theorem normalization_8169 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((c3_node % (2 : Int)) ≥ (1 : Int)))) ↔ (shared_expr_Repair114_51 c3_node) := (iff_congr (normalization_8165 c3_node) (normalization_8168 c3_node))

-- Checked replay of monotonicity.
theorem replay_7699 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ (True ∧ ((c3_node % (2 : Int)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2469 ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int)) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ↔ True) := by
    exact Iff.mp (normalization_8167 c3_node) (replay_7698 c3_node)
  have hn := ht n0
  exact Iff.mpr (normalization_8169 c3_node) hn

theorem normalized_2470 (p0 : Prop) : ((True ∧ p0) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8170 (c3_node : Int) : ((True ∧ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ ((True ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := (iff_congr (normalization_8168 c3_node) (normalization_7591 c3_node))

-- Checked replay of rewrite.
theorem replay_7700 (c3_node : Int) : ((True ∧ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c3_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_2470 ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8170 c3_node) hn

theorem normalized_2471 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_52 (c3_node : Int) : Prop := (((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
theorem normalization_8171 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ (shared_expr_Repair114_52 c3_node) := (iff_congr (normalization_8165 c3_node) (normalization_7591 c3_node))

-- Checked replay of trans.
theorem replay_7701 (c3_node : Int) : ((((c3_node % (2 : Int)) ≤ (1 : Int)) ∧ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ ((c3_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_2471 ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) (True ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair114_51 c3_node) := by
    exact Iff.mp (normalization_8169 c3_node) (replay_7699 c3_node)
  have n1 : ((True ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
    exact Iff.mp (normalization_8170 c3_node) (replay_7700 c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8171 c3_node) hn

theorem normalized_2472 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8172 (c3_node : Int) : (((c3_node % (2 : Int)) = (1 : Int)) ↔ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ (shared_expr_Repair114_52 c3_node) := (iff_congr (normalization_7116 c3_node) (normalization_7591 c3_node))

-- Checked replay of trans.
theorem replay_7702 (c3_node : Int) : (((c3_node % (2 : Int)) = (1 : Int)) ↔ ((c3_node % (2 : Int)) ≥ (1 : Int))) := by
  classical
  have ht := (normalized_2472 ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) (shared_expr_Repair114_52 c3_node))
  have n0 : (shared_expr_Repair114_50 c3_node) := by
    exact Iff.mp (normalization_8166 c3_node) (replay_7697 c3_node)
  have n1 : (shared_expr_Repair114_52 c3_node) := by
    exact Iff.mp (normalization_8171 c3_node) (replay_7701 c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8172 c3_node) hn

abbrev shared_expr_Repair114_53 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ∧ ((c3_node % (2 : Int)) ≥ (1 : Int)))
abbrev formula_2855 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := (shared_expr_Repair114_53 c3_depth c3_kind c3_node c3_sign r1_level)

theorem normalized_2473 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ p7)) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ p7))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_54 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
theorem normalization_8173 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (formula_2855 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Repair114_54 c3_depth c3_kind c3_node c3_sign r1_level) := (and_congr (normalization_6932 c3_kind) (and_congr (normalization_8133 c3_depth r1_level) (and_congr (normalization_7559 c3_sign) (normalization_7591 c3_node))))

abbrev shared_expr_Repair114_55 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
theorem normalization_8174 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int))) ↔ (formula_2855 c3_depth c3_kind c3_node c3_sign r1_level)) ↔ ((shared_expr_Repair114_55 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Repair114_54 c3_depth c3_kind c3_node c3_sign r1_level)) := (iff_congr (normalization_7910 c3_depth c3_kind c3_node c3_sign r1_level) (normalization_8173 c3_depth c3_kind c3_node c3_sign r1_level))

-- Checked replay of monotonicity.
theorem replay_7703 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int))) ↔ (formula_2855 c3_depth c3_kind c3_node c3_sign r1_level)) := by
  classical
  have ht := (normalized_2473 (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6934 c3_kind) (replay_6116 c3_kind)
  have n1 : (shared_expr_Repair114_30 c3_depth r1_level) := by
    exact Iff.mp (normalization_8136 c3_depth r1_level) (replay_7681 c3_depth r1_level)
  have n2 : (shared_expr_Repair114_37 c3_sign) := by
    exact Iff.mp (normalization_8082 c3_sign) (replay_7655 c3_sign)
  have n3 : (shared_expr_Repair114_52 c3_node) := by
    exact Iff.mp (normalization_8172 c3_node) (replay_7702 c3_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_8174 c3_depth c3_kind c3_node c3_sign r1_level) hn

theorem normalized_2474 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ p5) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_56 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_8175 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (formula_2596 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level) := (or_congr (normalization_6929 c3_kind) (or_congr (normalization_6930 c3_kind) (or_congr (normalization_7560 c3_sign) (or_congr (normalization_7592 c3_node) (or_congr (normalization_8130 c3_depth r1_level) (normalization_8131 c3_depth r1_level))))))

theorem normalization_8176 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (¬ (formula_2596 c3_depth c3_kind c3_node c3_sign r1_level)) ↔ (¬ (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level)) := (not_congr (normalization_8175 c3_depth c3_kind c3_node c3_sign r1_level))

theorem normalization_8177 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : ((formula_2855 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (formula_2596 c3_depth c3_kind c3_node c3_sign r1_level))) ↔ ((shared_expr_Repair114_54 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))) := (iff_congr (normalization_8173 c3_depth c3_kind c3_node c3_sign r1_level) (normalization_8176 c3_depth c3_kind c3_node c3_sign r1_level))

-- Checked replay of rewrite.
theorem replay_7704 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : ((formula_2855 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (formula_2596 c3_depth c3_kind c3_node c3_sign r1_level))) := by
  classical
  have ht := (normalized_2474 ((c3_kind) ≤ (1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8177 c3_depth c3_kind c3_node c3_sign r1_level) hn

theorem normalized_2475 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_57 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := (((c3_kind = (1 : Int)) ∧ (c3_depth = r1_level) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (2 : Int))) ∧ ((c3_node % (2 : Int)) = (1 : Int))) ↔ (¬ (formula_2596 c3_depth c3_kind c3_node c3_sign r1_level)))
theorem normalization_8178 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (shared_expr_Repair114_57 c3_depth c3_kind c3_node c3_sign r1_level) ↔ ((shared_expr_Repair114_55 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))) := (iff_congr (normalization_7910 c3_depth c3_kind c3_node c3_sign r1_level) (normalization_8176 c3_depth c3_kind c3_node c3_sign r1_level))

-- Checked replay of trans.
theorem replay_7705 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (shared_expr_Repair114_57 c3_depth c3_kind c3_node c3_sign r1_level) := by
  classical
  have ht := (normalized_2475 (shared_expr_Repair114_55 c3_depth c3_kind c3_node c3_sign r1_level) (shared_expr_Repair114_54 c3_depth c3_kind c3_node c3_sign r1_level) (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))
  have n0 : ((shared_expr_Repair114_55 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Repair114_54 c3_depth c3_kind c3_node c3_sign r1_level)) := by
    exact Iff.mp (normalization_8174 c3_depth c3_kind c3_node c3_sign r1_level) (replay_7703 c3_depth c3_kind c3_node c3_sign r1_level)
  have n1 : ((shared_expr_Repair114_54 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))) := by
    exact Iff.mp (normalization_8177 c3_depth c3_kind c3_node c3_sign r1_level) (replay_7704 c3_depth c3_kind c3_node c3_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8178 c3_depth c3_kind c3_node c3_sign r1_level) hn

abbrev shared_expr_Repair114_58 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_2596 c3_depth c3_kind c3_node c3_sign r1_level))))
abbrev formula_2856 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair114_58 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

theorem normalized_2476 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_59 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))))
theorem normalization_8179 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2856 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_59 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_8086 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_8176 c3_depth c3_kind c3_node c3_sign r1_level)))

abbrev shared_expr_Repair114_60 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair114_55 c3_depth c3_kind c3_node c3_sign r1_level)))
theorem normalization_8180 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2819 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2856 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_60 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_59 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (iff_congr (normalization_7974 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (normalization_8179 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_7706 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2819 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2856 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2476 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_55 c3_depth c3_kind c3_node c3_sign r1_level) (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((shared_expr_Repair114_3 c3_depth c3_kind c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))) := by
    exact Iff.mp (normalization_8088 c3_depth c3_kind c3_sign r1_level) (replay_7658 c3_depth c3_kind c3_sign r1_level)
  have n2 : ((shared_expr_Repair114_55 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (¬ (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))) := by
    exact Iff.mp (normalization_8178 c3_depth c3_kind c3_node c3_sign r1_level) (replay_7705 c3_depth c3_kind c3_node c3_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8180 c3_depth c3_kind c3_node c3_sign r1_group r1_level) hn

theorem normalized_2477 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair114_61 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level))))
theorem normalization_8181 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_8176 c3_depth c3_kind c3_node c3_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_8086 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_8182 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2856 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_59 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (iff_congr (normalization_8179 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (normalization_8181 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_7707 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2856 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2477 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (shared_expr_Repair114_1 c3_depth c3_kind c3_sign r1_level) (shared_expr_Repair114_56 c3_depth c3_kind c3_node c3_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_8182 c3_depth c3_kind c3_node c3_sign r1_group r1_level) hn

theorem normalized_2478 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8183 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2819 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((shared_expr_Repair114_60 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (iff_congr (normalization_7974 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (normalization_8181 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_7708 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : ((formula_2819 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_2478 (shared_expr_Repair114_60 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (shared_expr_Repair114_59 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair114_60 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_59 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8180 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (replay_7706 c3_depth c3_kind c3_node c3_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair114_59 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8182 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (replay_7707 c3_depth c3_kind c3_node c3_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8183 c3_depth c3_kind c3_node c3_sign r1_group r1_level) hn

abbrev shared_expr_Repair114_62 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (3 : Int)) ∧ (formula_2819 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))))) ∧ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
abbrev formula_2857 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair114_62 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

theorem normalized_2479 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8184 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))))) ∧ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (and_congr (normalization_3617 r1_mode) (normalization_8181 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

abbrev shared_expr_Repair114_63 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair114_60 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))))) ∧ (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
theorem normalization_8185 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2857 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair114_63 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_7975 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (normalization_8184 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_7709 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2857 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_2479 (((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))) (shared_expr_Repair114_60 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int))))))) := by
    exact Iff.mp (normalization_3619 r1_mode) (replay_2431 r1_mode)
  have n1 : ((shared_expr_Repair114_60 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Repair114_61 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_8183 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (replay_7708 c3_depth c3_kind c3_node c3_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8185 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) hn

end H4Formal.Generated.Repair
