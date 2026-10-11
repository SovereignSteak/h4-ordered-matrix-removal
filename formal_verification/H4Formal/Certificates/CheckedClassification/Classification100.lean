import H4Formal.Certificates.CheckedClassification.Classification099

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_6539 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i432 : (formula_2637 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2652 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_6538 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_6537 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i432)

abbrev shared_expr_Classification100_0 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : Prop := ((((c0_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2645 c0_group c0_level c0_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))
abbrev shared_expr_Classification100_1 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : Prop := ((((c0_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2628 c0_group c0_level c0_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))
abbrev formula_2654 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : Prop := ((shared_expr_Classification100_0 c0_group c0_level c0_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification100_1 c0_group c0_level c0_mode c3_group c3_level c3_mode))

theorem normalized_2304 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8101 (c0_level c3_level : Int) : ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_8102 (c0_level c3_level : Int) : (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) := (not_congr (normalization_8101 c0_level c3_level))

theorem normalization_8103 (c0_level c3_level : Int) : ((¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ ((¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) := (or_congr (normalization_8102 c0_level c3_level) (normalization_8075 c0_level c3_level))

theorem normalization_8104 (c0_mode c3_mode : Int) : ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_8105 (c0_mode c3_mode : Int) : (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) := (not_congr (normalization_8104 c0_mode c3_mode))

theorem normalization_8106 (c0_mode c3_mode : Int) : ((¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_8105 c0_mode c3_mode) (normalization_8072 c0_mode c3_mode))

abbrev shared_expr_Classification100_2 (c0_group c0_mode c3_group c3_mode : Int) : Prop := ((((¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))))
theorem normalization_8107 (c0_group c0_mode c3_group c3_mode : Int) : (formula_2627 c0_group c0_mode c3_group c3_mode) ↔ (shared_expr_Classification100_2 c0_group c0_mode c3_group c3_mode) := (or_congr (and_congr (normalization_8106 c0_mode c3_mode) (normalization_8072 c0_mode c3_mode)) (and_congr (not_congr (normalization_8106 c0_mode c3_mode)) (normalization_8070 c0_group c3_group)))

abbrev shared_expr_Classification100_3 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification100_2 c0_group c0_mode c3_group c3_mode)))
theorem normalization_8108 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : (formula_2628 c0_group c0_level c0_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification100_3 c0_group c0_level c0_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_8103 c0_level c3_level) (normalization_8075 c0_level c3_level)) (and_congr (not_congr (normalization_8103 c0_level c3_level)) (normalization_8107 c0_group c0_mode c3_group c3_mode)))

abbrev shared_expr_Classification100_4 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification100_3 c0_group c0_level c0_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_8109 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : (shared_expr_Classification100_1 c0_group c0_level c0_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_8035 c0_mode c3_mode) (normalization_8108 c0_group c0_level c0_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_8035 c0_mode c3_mode)) (normalization_3411 c0_mode)))

abbrev shared_expr_Classification100_5 (c0_group c0_mode c3_group c3_mode : Int) : Prop := (((((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification100_6 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : Prop := (((((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification100_5 c0_group c0_mode c3_group c3_mode)) ∨ ((¬ (((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification100_7 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification100_6 c0_group c0_level c0_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_8110 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : (formula_2654 c0_group c0_level c0_mode c3_group c3_level c3_mode) ↔ ((shared_expr_Classification100_7 c0_group c0_level c0_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)) := (iff_congr (normalization_8077 c0_group c0_level c0_mode c3_group c3_level c3_mode) (normalization_8109 c0_group c0_level c0_mode c3_group c3_level c3_mode))

-- Checked replay of rewrite.
theorem replay_6540 (c0_group c0_level c0_mode c3_group c3_level c3_mode : Int) : (formula_2654 c0_group c0_level c0_mode c3_group c3_level c3_mode) := by
  classical
  have ht := (normalized_2304 ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ((c0_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)) ((c0_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8110 c0_group c0_level c0_mode c3_group c3_level c3_mode) hn

abbrev formula_2655 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ∨ (shared_expr_Classification100_1 c0_group c0_level c0_mode c3_group c3_level c3_mode))

theorem normalized_2305 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8111 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2655 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6745 c3_kind) (normalization_8109 c0_group c0_level c0_mode c3_group c3_level c3_mode))

abbrev shared_expr_Classification100_8 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_7 c0_group c0_level c0_mode c3_group c3_level c3_mode)) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)))
theorem normalization_8112 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2646 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2655 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification100_8 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_8078 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) (normalization_8111 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of monotonicity.
theorem replay_6541 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2646 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2655 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2305 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification100_7 c0_group c0_level c0_mode c3_group c3_level c3_mode) (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode))
  have n0 : ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_7265 c3_kind) (replay_5101 c3_kind)
  have n1 : ((shared_expr_Classification100_7 c0_group c0_level c0_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)) := by
    exact Iff.mp (normalization_8110 c0_group c0_level c0_mode c3_group c3_level c3_mode) (replay_6540 c0_group c0_level c0_mode c3_group c3_level c3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8112 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2306 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8113 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2629 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6743 c3_kind) (or_congr (normalization_6744 c3_kind) (normalization_8109 c0_group c0_level c0_mode c3_group c3_level c3_mode)))

abbrev shared_expr_Classification100_9 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)))
theorem normalization_8114 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2655 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2629 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification100_9 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_8111 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) (normalization_8113 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of rewrite.
theorem replay_6542 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2655 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2629 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2306 ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)) (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode))
  have hn := ht
  exact Iff.mpr (normalization_8114 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2307 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_10 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_7 c0_group c0_level c0_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)))
theorem normalization_8115 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2646 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2629 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Classification100_10 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_8078 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) (normalization_8113 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of trans.
theorem replay_6543 (c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2646 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2629 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2307 ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_7 c0_group c0_level c0_mode c3_group c3_level c3_mode)) (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification100_4 c0_group c0_level c0_mode c3_group c3_level c3_mode)))
  have n0 : (shared_expr_Classification100_8 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_8112 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) (replay_6541 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode)
  have n1 : (shared_expr_Classification100_9 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_8114 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) (replay_6542 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8115 c0_group c0_level c0_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2308 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8116 (c0_depth c3_depth : Int) : (c0_depth ≤ c3_depth) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_8117 (c0_depth c3_depth : Int) : (c0_depth ≥ c3_depth) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8118 (c0_depth c3_depth : Int) : ((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_8116 c0_depth c3_depth) (normalization_8117 c0_depth c3_depth))

abbrev shared_expr_Classification100_11 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
theorem normalization_8119 (c0_depth c3_depth : Int) : ((c0_depth = c3_depth) ↔ ((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth))) ↔ (shared_expr_Classification100_11 c0_depth c3_depth) := (iff_congr (normalization_8015 c0_depth c3_depth) (normalization_8118 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6544 (c0_depth c3_depth : Int) : ((c0_depth = c3_depth) ↔ ((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth))) := by
  classical
  have ht := (normalized_2308 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8119 c0_depth c3_depth) hn

theorem normalized_2309 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8120 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_8121 (c0_depth c3_depth : Int) : ((c0_depth ≤ c3_depth) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := (iff_congr (normalization_8116 c0_depth c3_depth) (normalization_8120 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6545 (c0_depth c3_depth : Int) : ((c0_depth ≤ c3_depth) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2309 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8121 c0_depth c3_depth) hn

theorem normalized_2310 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8122 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8123 (c0_depth c3_depth : Int) : ((c0_depth ≥ c3_depth) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_8117 c0_depth c3_depth) (normalization_8122 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6546 (c0_depth c3_depth : Int) : ((c0_depth ≥ c3_depth) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2310 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8123 c0_depth c3_depth) hn

theorem normalized_2311 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8124 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_8120 c0_depth c3_depth) (normalization_8122 c0_depth c3_depth))

theorem normalization_8125 (c0_depth c3_depth : Int) : (((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification100_11 c0_depth c3_depth) := (iff_congr (normalization_8118 c0_depth c3_depth) (normalization_8124 c0_depth c3_depth))

-- Checked replay of monotonicity.
theorem replay_6547 (c0_depth c3_depth : Int) : (((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2311 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
  have n0 : (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8121 c0_depth c3_depth) (replay_6545 c0_depth c3_depth)
  have n1 : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8123 c0_depth c3_depth) (replay_6546 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8125 c0_depth c3_depth) hn

abbrev shared_expr_Classification100_12 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))))
abbrev formula_2656 (c0_depth c3_depth : Int) : Prop := (shared_expr_Classification100_12 c0_depth c3_depth)

theorem normalized_2312 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8126 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := (not_congr (normalization_8120 c0_depth c3_depth))

theorem normalization_8127 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_8122 c0_depth c3_depth))

theorem normalization_8128 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_8126 c0_depth c3_depth) (normalization_8127 c0_depth c3_depth))

theorem normalization_8129 (c0_depth c3_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_8128 c0_depth c3_depth))

abbrev shared_expr_Classification100_13 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))))
theorem normalization_8130 (c0_depth c3_depth : Int) : (formula_2656 c0_depth c3_depth) ↔ (shared_expr_Classification100_13 c0_depth c3_depth) := (iff_congr (normalization_8124 c0_depth c3_depth) (normalization_8129 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6548 (c0_depth c3_depth : Int) : (formula_2656 c0_depth c3_depth) := by
  classical
  have ht := (normalized_2312 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8130 c0_depth c3_depth) hn

theorem normalized_2313 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8131 (c0_depth c3_depth : Int) : (((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification100_13 c0_depth c3_depth) := (iff_congr (normalization_8118 c0_depth c3_depth) (normalization_8129 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_6549 (c0_depth c3_depth : Int) : (((c0_depth ≤ c3_depth) ∧ (c0_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2313 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Classification100_13 c0_depth c3_depth))
  have n0 : (shared_expr_Classification100_11 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8125 c0_depth c3_depth) (replay_6547 c0_depth c3_depth)
  have n1 : (shared_expr_Classification100_13 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8130 c0_depth c3_depth) (replay_6548 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8131 c0_depth c3_depth) hn

theorem normalized_2314 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8132 (c0_depth c3_depth : Int) : ((c0_depth = c3_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification100_13 c0_depth c3_depth) := (iff_congr (normalization_8015 c0_depth c3_depth) (normalization_8129 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_6550 (c0_depth c3_depth : Int) : ((c0_depth = c3_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2314 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Classification100_13 c0_depth c3_depth))
  have n0 : (shared_expr_Classification100_11 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8119 c0_depth c3_depth) (replay_6544 c0_depth c3_depth)
  have n1 : (shared_expr_Classification100_13 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8131 c0_depth c3_depth) (replay_6549 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8132 c0_depth c3_depth) hn

theorem normalized_2315 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8133 (c0_node c3_node : Int) : (c0_node ≤ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_8134 (c0_node c3_node : Int) : (c0_node ≥ c3_node) ↔ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8135 (c0_node c3_node : Int) : ((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_8133 c0_node c3_node) (normalization_8134 c0_node c3_node))

abbrev shared_expr_Classification100_14 (c0_node c3_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_8136 (c0_node c3_node : Int) : ((c0_node = c3_node) ↔ ((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node))) ↔ (shared_expr_Classification100_14 c0_node c3_node) := (iff_congr (normalization_8016 c0_node c3_node) (normalization_8135 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_6551 (c0_node c3_node : Int) : ((c0_node = c3_node) ↔ ((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node))) := by
  classical
  have ht := (normalized_2315 (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8136 c0_node c3_node) hn

theorem normalized_2316 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8137 (c0_node c3_node : Int) : ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_8138 (c0_node c3_node : Int) : ((c0_node ≤ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (iff_congr (normalization_8133 c0_node c3_node) (normalization_8137 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_6552 (c0_node c3_node : Int) : ((c0_node ≤ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2316 ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8138 c0_node c3_node) hn

theorem normalized_2317 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8139 (c0_node c3_node : Int) : ((c0_node ≥ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_8134 c0_node c3_node) (normalization_8079 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_6553 (c0_node c3_node : Int) : ((c0_node ≥ c3_node) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2317 ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8139 c0_node c3_node) hn

theorem normalized_2318 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8140 (c0_node c3_node : Int) : (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_8137 c0_node c3_node) (normalization_8079 c0_node c3_node))

theorem normalization_8141 (c0_node c3_node : Int) : (((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification100_14 c0_node c3_node) := (iff_congr (normalization_8135 c0_node c3_node) (normalization_8140 c0_node c3_node))

-- Checked replay of monotonicity.
theorem replay_6554 (c0_node c3_node : Int) : (((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2318 ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have n0 : (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8138 c0_node c3_node) (replay_6552 c0_node c3_node)
  have n1 : ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8139 c0_node c3_node) (replay_6553 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8141 c0_node c3_node) hn

abbrev shared_expr_Classification100_15 (c0_node c3_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))))
abbrev formula_2657 (c0_node c3_node : Int) : Prop := (shared_expr_Classification100_15 c0_node c3_node)

theorem normalized_2319 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8142 (c0_node c3_node : Int) : (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_8137 c0_node c3_node))

theorem normalization_8143 (c0_node c3_node : Int) : ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_8142 c0_node c3_node) (normalization_8080 c0_node c3_node))

theorem normalization_8144 (c0_node c3_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_8143 c0_node c3_node))

abbrev shared_expr_Classification100_16 (c0_node c3_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))))
theorem normalization_8145 (c0_node c3_node : Int) : (formula_2657 c0_node c3_node) ↔ (shared_expr_Classification100_16 c0_node c3_node) := (iff_congr (normalization_8140 c0_node c3_node) (normalization_8144 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_6555 (c0_node c3_node : Int) : (formula_2657 c0_node c3_node) := by
  classical
  have ht := (normalized_2319 ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8145 c0_node c3_node) hn

theorem normalized_2320 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8146 (c0_node c3_node : Int) : (((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification100_16 c0_node c3_node) := (iff_congr (normalization_8135 c0_node c3_node) (normalization_8144 c0_node c3_node))

-- Checked replay of trans.
theorem replay_6556 (c0_node c3_node : Int) : (((c0_node ≤ c3_node) ∧ (c0_node ≥ c3_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2320 (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Classification100_16 c0_node c3_node))
  have n0 : (shared_expr_Classification100_14 c0_node c3_node) := by
    exact Iff.mp (normalization_8141 c0_node c3_node) (replay_6554 c0_node c3_node)
  have n1 : (shared_expr_Classification100_16 c0_node c3_node) := by
    exact Iff.mp (normalization_8145 c0_node c3_node) (replay_6555 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8146 c0_node c3_node) hn

theorem normalized_2321 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8147 (c0_node c3_node : Int) : ((c0_node = c3_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification100_16 c0_node c3_node) := (iff_congr (normalization_8016 c0_node c3_node) (normalization_8144 c0_node c3_node))

-- Checked replay of trans.
theorem replay_6557 (c0_node c3_node : Int) : ((c0_node = c3_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2321 (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Classification100_16 c0_node c3_node))
  have n0 : (shared_expr_Classification100_14 c0_node c3_node) := by
    exact Iff.mp (normalization_8136 c0_node c3_node) (replay_6551 c0_node c3_node)
  have n1 : (shared_expr_Classification100_16 c0_node c3_node) := by
    exact Iff.mp (normalization_8146 c0_node c3_node) (replay_6556 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8147 c0_node c3_node) hn

theorem normalized_2322 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8148 (c0_sign c3_sign : Int) : ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (and_congr (normalization_3582 c0_sign) (normalization_6849 c3_sign))

abbrev shared_expr_Classification100_17 (c0_sign c3_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))))
theorem normalization_8149 (c0_sign c3_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) ↔ (shared_expr_Classification100_17 c0_sign c3_sign) := (iff_congr (normalization_8017 c0_sign c3_sign) (normalization_8148 c0_sign c3_sign))

-- Checked replay of monotonicity.
theorem replay_6558 (c0_sign c3_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_2322 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3584 c0_sign) (replay_1316 c0_sign)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6942 c3_sign) (replay_4980 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8149 c0_sign c3_sign) hn

abbrev shared_expr_Classification100_18 (c0_sign c3_sign : Int) : Prop := (((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev formula_2658 (c0_sign c3_sign : Int) : Prop := (shared_expr_Classification100_18 c0_sign c3_sign)

theorem normalized_2323 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8150 (c0_sign c3_sign : Int) : ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ↔ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) := (or_congr (normalization_3579 c0_sign) (or_congr (normalization_3580 c0_sign) (or_congr (normalization_6845 c3_sign) (normalization_6847 c3_sign))))

theorem normalization_8151 (c0_sign c3_sign : Int) : (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_8150 c0_sign c3_sign))

abbrev shared_expr_Classification100_19 (c0_sign c3_sign : Int) : Prop := (((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_8152 (c0_sign c3_sign : Int) : (formula_2658 c0_sign c3_sign) ↔ (shared_expr_Classification100_19 c0_sign c3_sign) := (iff_congr (normalization_8148 c0_sign c3_sign) (normalization_8151 c0_sign c3_sign))

-- Checked replay of rewrite.
theorem replay_6559 (c0_sign c3_sign : Int) : (formula_2658 c0_sign c3_sign) := by
  classical
  have ht := (normalized_2323 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8152 c0_sign c3_sign) hn

theorem normalized_2324 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_20 (c0_sign c3_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_8153 (c0_sign c3_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (shared_expr_Classification100_20 c0_sign c3_sign) := (iff_congr (normalization_8017 c0_sign c3_sign) (normalization_8151 c0_sign c3_sign))

-- Checked replay of trans.
theorem replay_6560 (c0_sign c3_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2324 ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification100_17 c0_sign c3_sign) := by
    exact Iff.mp (normalization_8149 c0_sign c3_sign) (replay_6558 c0_sign c3_sign)
  have n1 : (shared_expr_Classification100_19 c0_sign c3_sign) := by
    exact Iff.mp (normalization_8152 c0_sign c3_sign) (replay_6559 c0_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8153 c0_sign c3_sign) hn

abbrev shared_expr_Classification100_21 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification100_22 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification100_21 c0_node c0_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))
abbrev formula_2659 (c0_node c0_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification100_22 c0_node c0_sign c3_node c3_sign)

abbrev shared_expr_Classification100_23 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((((c0_node = c3_node) ∧ ((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c0_node = c3_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_2659 c0_node c0_sign c3_node c3_sign))
abbrev formula_2660 (c0_node c0_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification100_23 c0_node c0_sign c3_node c3_sign)

theorem normalized_2325 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_24 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification100_25 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification100_24 c0_node c0_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_8154 (c0_node c0_sign c3_node c3_sign : Int) : (formula_2659 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Classification100_25 c0_node c0_sign c3_node c3_sign) := (or_congr (and_congr (normalization_8144 c0_node c3_node) (normalization_8151 c0_sign c3_sign)) (and_congr (not_congr (normalization_8144 c0_node c3_node)) (normalization_8080 c0_node c3_node)))

abbrev shared_expr_Classification100_26 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification100_27 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification100_26 c0_node c0_sign c3_node c3_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_8155 (c0_node c0_sign c3_node c3_sign : Int) : (formula_2660 c0_node c0_sign c3_node c3_sign) ↔ ((shared_expr_Classification100_27 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Classification100_25 c0_node c0_sign c3_node c3_sign)) := (iff_congr (normalization_8081 c0_node c0_sign c3_node c3_sign) (normalization_8154 c0_node c0_sign c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_6561 (c0_node c0_sign c3_node c3_sign : Int) : (formula_2660 c0_node c0_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_2325 (((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification100_16 c0_node c3_node) := by
    exact Iff.mp (normalization_8147 c0_node c3_node) (replay_6557 c0_node c3_node)
  have n1 : (shared_expr_Classification100_20 c0_sign c3_sign) := by
    exact Iff.mp (normalization_8153 c0_sign c3_sign) (replay_6560 c0_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8155 c0_node c0_sign c3_node c3_sign) hn

theorem normalized_2326 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_28 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_24 c0_node c0_sign c3_node c3_sign))
theorem normalization_8156 (c0_node c0_sign c3_node c3_sign : Int) : (formula_2623 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Classification100_28 c0_node c0_sign c3_node c3_sign) := (or_congr (and_congr (normalization_8143 c0_node c3_node) (normalization_8080 c0_node c3_node)) (and_congr (not_congr (normalization_8143 c0_node c3_node)) (normalization_8151 c0_sign c3_sign)))

theorem normalization_8157 (c0_node c0_sign c3_node c3_sign : Int) : ((formula_2659 c0_node c0_sign c3_node c3_sign) ↔ (formula_2623 c0_node c0_sign c3_node c3_sign)) ↔ ((shared_expr_Classification100_25 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Classification100_28 c0_node c0_sign c3_node c3_sign)) := (iff_congr (normalization_8154 c0_node c0_sign c3_node c3_sign) (normalization_8156 c0_node c0_sign c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_6562 (c0_node c0_sign c3_node c3_sign : Int) : ((formula_2659 c0_node c0_sign c3_node c3_sign) ↔ (formula_2623 c0_node c0_sign c3_node c3_sign)) := by
  classical
  have ht := (normalized_2326 ((¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8157 c0_node c0_sign c3_node c3_sign) hn

abbrev shared_expr_Classification100_29 (c0_node c0_sign c3_node c3_sign : Int) : Prop := ((((c0_node = c3_node) ∧ ((c0_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c0_node = c3_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_2623 c0_node c0_sign c3_node c3_sign))
abbrev formula_2661 (c0_node c0_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification100_29 c0_node c0_sign c3_node c3_sign)

theorem normalized_2327 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8158 (c0_node c0_sign c3_node c3_sign : Int) : (formula_2661 c0_node c0_sign c3_node c3_sign) ↔ ((shared_expr_Classification100_27 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Classification100_28 c0_node c0_sign c3_node c3_sign)) := (iff_congr (normalization_8081 c0_node c0_sign c3_node c3_sign) (normalization_8156 c0_node c0_sign c3_node c3_sign))

-- Checked replay of trans.
theorem replay_6563 (c0_node c0_sign c3_node c3_sign : Int) : (formula_2661 c0_node c0_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_2327 (shared_expr_Classification100_27 c0_node c0_sign c3_node c3_sign) (shared_expr_Classification100_25 c0_node c0_sign c3_node c3_sign) (shared_expr_Classification100_28 c0_node c0_sign c3_node c3_sign))
  have n0 : ((shared_expr_Classification100_27 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Classification100_25 c0_node c0_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_8155 c0_node c0_sign c3_node c3_sign) (replay_6561 c0_node c0_sign c3_node c3_sign)
  have n1 : ((shared_expr_Classification100_25 c0_node c0_sign c3_node c3_sign) ↔ (shared_expr_Classification100_28 c0_node c0_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_8157 c0_node c0_sign c3_node c3_sign) (replay_6562 c0_node c0_sign c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8158 c0_node c0_sign c3_node c3_sign) hn

theorem normalized_2328 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8159 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_8160 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_8161 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_8159 c0_depth c3_depth) (normalization_8160 c0_depth c3_depth))

abbrev shared_expr_Classification100_30 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
theorem normalization_8162 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Classification100_30 c0_depth c3_depth) := (iff_congr (normalization_8082 c0_depth c3_depth) (normalization_8161 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6564 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_2328 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8162 c0_depth c3_depth) hn

abbrev shared_expr_Classification100_31 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))))
abbrev formula_2662 (c0_depth c3_depth : Int) : Prop := (shared_expr_Classification100_31 c0_depth c3_depth)

theorem normalized_2329 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8163 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := (not_congr (normalization_8159 c0_depth c3_depth))

theorem normalization_8164 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_8160 c0_depth c3_depth))

theorem normalization_8165 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_8163 c0_depth c3_depth) (normalization_8164 c0_depth c3_depth))

theorem normalization_8166 (c0_depth c3_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_8165 c0_depth c3_depth))

abbrev shared_expr_Classification100_32 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))))
theorem normalization_8167 (c0_depth c3_depth : Int) : (formula_2662 c0_depth c3_depth) ↔ (shared_expr_Classification100_32 c0_depth c3_depth) := (iff_congr (normalization_8161 c0_depth c3_depth) (normalization_8166 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6565 (c0_depth c3_depth : Int) : (formula_2662 c0_depth c3_depth) := by
  classical
  have ht := (normalized_2329 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8167 c0_depth c3_depth) hn

theorem normalized_2330 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8168 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Classification100_32 c0_depth c3_depth) := (iff_congr (normalization_8082 c0_depth c3_depth) (normalization_8166 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_6566 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_2330 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Classification100_32 c0_depth c3_depth))
  have n0 : (shared_expr_Classification100_30 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8162 c0_depth c3_depth) (replay_6564 c0_depth c3_depth)
  have n1 : (shared_expr_Classification100_32 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8167 c0_depth c3_depth) (replay_6565 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8168 c0_depth c3_depth) hn

theorem normalized_2331 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8169 (c0_node c3_node : Int) : ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8170 (c0_node c3_node : Int) : (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (and_congr (normalization_8169 c0_node c3_node) (normalization_8084 c0_node c3_node))

abbrev shared_expr_Classification100_33 (c0_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_8171 (c0_node c3_node : Int) : (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification100_33 c0_node c3_node) := (iff_congr (normalization_8083 c0_node c3_node) (normalization_8170 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_6567 (c0_node c3_node : Int) : (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2331 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8171 c0_node c3_node) hn

abbrev shared_expr_Classification100_34 (c0_node c3_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2663 (c0_node c3_node : Int) : Prop := (shared_expr_Classification100_34 c0_node c3_node)

theorem normalized_2332 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8172 (c0_node c3_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_8169 c0_node c3_node))

theorem normalization_8173 (c0_node c3_node : Int) : ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) := (or_congr (normalization_8172 c0_node c3_node) (normalization_8085 c0_node c3_node))

theorem normalization_8174 (c0_node c3_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) := (not_congr (normalization_8173 c0_node c3_node))

abbrev shared_expr_Classification100_35 (c0_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
theorem normalization_8175 (c0_node c3_node : Int) : (formula_2663 c0_node c3_node) ↔ (shared_expr_Classification100_35 c0_node c3_node) := (iff_congr (normalization_8170 c0_node c3_node) (normalization_8174 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_6568 (c0_node c3_node : Int) : (formula_2663 c0_node c3_node) := by
  classical
  have ht := (normalized_2332 (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)) (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8175 c0_node c3_node) hn

abbrev shared_expr_Classification100_36 (c0_node c3_node : Int) : Prop := (((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2664 (c0_node c3_node : Int) : Prop := (shared_expr_Classification100_36 c0_node c3_node)

theorem normalized_2333 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8176 (c0_node c3_node : Int) : (formula_2664 c0_node c3_node) ↔ (shared_expr_Classification100_35 c0_node c3_node) := (iff_congr (normalization_8083 c0_node c3_node) (normalization_8174 c0_node c3_node))

-- Checked replay of trans.
theorem replay_6569 (c0_node c3_node : Int) : (formula_2664 c0_node c3_node) := by
  classical
  have ht := (normalized_2333 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) (shared_expr_Classification100_35 c0_node c3_node))
  have n0 : (shared_expr_Classification100_33 c0_node c3_node) := by
    exact Iff.mp (normalization_8171 c0_node c3_node) (replay_6567 c0_node c3_node)
  have n1 : (shared_expr_Classification100_35 c0_node c3_node) := by
    exact Iff.mp (normalization_8175 c0_node c3_node) (replay_6568 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8176 c0_node c3_node) hn

abbrev shared_expr_Classification100_37 (c0_node c0_sign c3_node : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))))
abbrev shared_expr_Classification100_38 (c0_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2665 (c0_node c0_sign c3_node : Int) : Prop := ((shared_expr_Classification100_37 c0_node c0_sign c3_node) ∨ (shared_expr_Classification100_38 c0_node c3_node))

theorem normalized_2334 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_39 (c0_node c0_sign c3_node : Int) : Prop := ((¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Classification100_40 (c0_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_8177 (c0_node c0_sign c3_node : Int) : (formula_2665 c0_node c0_sign c3_node) ↔ ((shared_expr_Classification100_39 c0_node c0_sign c3_node) ∨ (shared_expr_Classification100_40 c0_node c3_node)) := (or_congr (and_congr (normalization_8174 c0_node c3_node) (normalization_3582 c0_sign)) (and_congr (not_congr (normalization_8174 c0_node c3_node)) (normalization_8085 c0_node c3_node)))

abbrev shared_expr_Classification100_41 (c0_node c3_node : Int) : Prop := ((¬ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification100_42 (c0_node c0_sign c3_node : Int) : Prop := ((((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Classification100_41 c0_node c3_node))
theorem normalization_8178 (c0_node c0_sign c3_node : Int) : ((formula_2647 c0_node c0_sign c3_node) ↔ (formula_2665 c0_node c0_sign c3_node)) ↔ ((shared_expr_Classification100_42 c0_node c0_sign c3_node) ↔ ((shared_expr_Classification100_39 c0_node c0_sign c3_node) ∨ (shared_expr_Classification100_40 c0_node c3_node))) := (iff_congr (normalization_8086 c0_node c0_sign c3_node) (normalization_8177 c0_node c0_sign c3_node))

-- Checked replay of monotonicity.
theorem replay_6570 (c0_node c0_sign c3_node : Int) : ((formula_2647 c0_node c0_sign c3_node) ↔ (formula_2665 c0_node c0_sign c3_node)) := by
  classical
  have ht := (normalized_2334 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Classification100_35 c0_node c3_node) := by
    exact Iff.mp (normalization_8176 c0_node c3_node) (replay_6569 c0_node c3_node)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3584 c0_sign) (replay_1316 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8178 c0_node c0_sign c3_node) hn

theorem normalized_2335 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_43 (c0_node c3_node : Int) : Prop := (((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_8179 (c0_node c0_sign c3_node : Int) : (formula_2621 c0_node c0_sign c3_node) ↔ ((shared_expr_Classification100_43 c0_node c3_node) ∨ (shared_expr_Classification100_39 c0_node c0_sign c3_node)) := (or_congr (and_congr (normalization_8173 c0_node c3_node) (normalization_8085 c0_node c3_node)) (and_congr (not_congr (normalization_8173 c0_node c3_node)) (normalization_3582 c0_sign)))

abbrev shared_expr_Classification100_44 (c0_node c0_sign c3_node : Int) : Prop := (((shared_expr_Classification100_39 c0_node c0_sign c3_node) ∨ (shared_expr_Classification100_40 c0_node c3_node)) ↔ ((shared_expr_Classification100_43 c0_node c3_node) ∨ (shared_expr_Classification100_39 c0_node c0_sign c3_node)))
theorem normalization_8180 (c0_node c0_sign c3_node : Int) : ((formula_2665 c0_node c0_sign c3_node) ↔ (formula_2621 c0_node c0_sign c3_node)) ↔ (shared_expr_Classification100_44 c0_node c0_sign c3_node) := (iff_congr (normalization_8177 c0_node c0_sign c3_node) (normalization_8179 c0_node c0_sign c3_node))

-- Checked replay of rewrite.
theorem replay_6571 (c0_node c0_sign c3_node : Int) : ((formula_2665 c0_node c0_sign c3_node) ↔ (formula_2621 c0_node c0_sign c3_node)) := by
  classical
  have ht := (normalized_2335 ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8180 c0_node c0_sign c3_node) hn

theorem normalized_2336 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8181 (c0_node c0_sign c3_node : Int) : ((formula_2647 c0_node c0_sign c3_node) ↔ (formula_2621 c0_node c0_sign c3_node)) ↔ ((shared_expr_Classification100_42 c0_node c0_sign c3_node) ↔ ((shared_expr_Classification100_43 c0_node c3_node) ∨ (shared_expr_Classification100_39 c0_node c0_sign c3_node))) := (iff_congr (normalization_8086 c0_node c0_sign c3_node) (normalization_8179 c0_node c0_sign c3_node))

-- Checked replay of trans.
theorem replay_6572 (c0_node c0_sign c3_node : Int) : ((formula_2647 c0_node c0_sign c3_node) ↔ (formula_2621 c0_node c0_sign c3_node)) := by
  classical
  have ht := (normalized_2336 (shared_expr_Classification100_42 c0_node c0_sign c3_node) ((shared_expr_Classification100_39 c0_node c0_sign c3_node) ∨ (shared_expr_Classification100_40 c0_node c3_node)) ((shared_expr_Classification100_43 c0_node c3_node) ∨ (shared_expr_Classification100_39 c0_node c0_sign c3_node)))
  have n0 : ((shared_expr_Classification100_42 c0_node c0_sign c3_node) ↔ ((shared_expr_Classification100_39 c0_node c0_sign c3_node) ∨ (shared_expr_Classification100_40 c0_node c3_node))) := by
    exact Iff.mp (normalization_8178 c0_node c0_sign c3_node) (replay_6570 c0_node c0_sign c3_node)
  have n1 : (shared_expr_Classification100_44 c0_node c0_sign c3_node) := by
    exact Iff.mp (normalization_8180 c0_node c0_sign c3_node) (replay_6571 c0_node c0_sign c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8181 c0_node c0_sign c3_node) hn

theorem normalized_2337 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8182 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_8183 (c0_depth c3_depth : Int) : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_8184 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (and_congr (normalization_8182 c0_depth c3_depth) (normalization_8183 c0_depth c3_depth))

abbrev shared_expr_Classification100_45 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
theorem normalization_8185 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification100_45 c0_depth c3_depth) := (iff_congr (normalization_8087 c0_depth c3_depth) (normalization_8184 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6573 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2337 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8185 c0_depth c3_depth) hn

abbrev shared_expr_Classification100_46 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))
abbrev formula_2666 (c0_depth c3_depth : Int) : Prop := (shared_expr_Classification100_46 c0_depth c3_depth)

theorem normalized_2338 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8186 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := (not_congr (normalization_8182 c0_depth c3_depth))

theorem normalization_8187 (c0_depth c3_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (not_congr (normalization_8183 c0_depth c3_depth))

theorem normalization_8188 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) := (or_congr (normalization_8186 c0_depth c3_depth) (normalization_8187 c0_depth c3_depth))

theorem normalization_8189 (c0_depth c3_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))) := (not_congr (normalization_8188 c0_depth c3_depth))

abbrev shared_expr_Classification100_47 (c0_depth c3_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))))
theorem normalization_8190 (c0_depth c3_depth : Int) : (formula_2666 c0_depth c3_depth) ↔ (shared_expr_Classification100_47 c0_depth c3_depth) := (iff_congr (normalization_8184 c0_depth c3_depth) (normalization_8189 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6574 (c0_depth c3_depth : Int) : (formula_2666 c0_depth c3_depth) := by
  classical
  have ht := (normalized_2338 ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8190 c0_depth c3_depth) hn

theorem normalized_2339 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8191 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification100_47 c0_depth c3_depth) := (iff_congr (normalization_8087 c0_depth c3_depth) (normalization_8189 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_6575 (c0_depth c3_depth : Int) : (((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2339 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (shared_expr_Classification100_47 c0_depth c3_depth))
  have n0 : (shared_expr_Classification100_45 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8185 c0_depth c3_depth) (replay_6573 c0_depth c3_depth)
  have n1 : (shared_expr_Classification100_47 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8190 c0_depth c3_depth) (replay_6574 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8191 c0_depth c3_depth) hn

theorem normalized_2340 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8192 (c0_depth c3_depth : Int) : (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))) := (not_congr (normalization_8189 c0_depth c3_depth))

abbrev shared_expr_Classification100_48 (c0_depth c3_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))))
theorem normalization_8193 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))) ↔ (shared_expr_Classification100_48 c0_depth c3_depth) := (iff_congr (normalization_8088 c0_depth c3_depth) (normalization_8192 c0_depth c3_depth))

-- Checked replay of monotonicity.
theorem replay_6576 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_2340 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification100_47 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8191 c0_depth c3_depth) (replay_6575 c0_depth c3_depth)
  have hn := ht n0
  exact Iff.mpr (normalization_8193 c0_depth c3_depth) hn

abbrev shared_expr_Classification100_49 (c0_depth c3_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))
abbrev formula_2667 (c0_depth c3_depth : Int) : Prop := (shared_expr_Classification100_49 c0_depth c3_depth)

theorem normalized_2341 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_50 (c0_depth c3_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
theorem normalization_8194 (c0_depth c3_depth : Int) : (formula_2667 c0_depth c3_depth) ↔ (shared_expr_Classification100_50 c0_depth c3_depth) := (iff_congr (normalization_8192 c0_depth c3_depth) (normalization_8188 c0_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6577 (c0_depth c3_depth : Int) : (formula_2667 c0_depth c3_depth) := by
  classical
  have ht := (normalized_2341 ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_8194 c0_depth c3_depth) hn

theorem normalized_2342 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_51 (c0_depth c3_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
theorem normalization_8195 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (shared_expr_Classification100_51 c0_depth c3_depth) := (iff_congr (normalization_8088 c0_depth c3_depth) (normalization_8188 c0_depth c3_depth))

-- Checked replay of trans.
theorem replay_6578 (c0_depth c3_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) := by
  classical
  have ht := (normalized_2342 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification100_48 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8193 c0_depth c3_depth) (replay_6576 c0_depth c3_depth)
  have n1 : (shared_expr_Classification100_50 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8194 c0_depth c3_depth) (replay_6577 c0_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8195 c0_depth c3_depth) hn

theorem normalized_2343 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8196 (c0_node c3_node : Int) : ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_8197 (c0_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (and_congr (normalization_8090 c0_node c3_node) (normalization_8196 c0_node c3_node))

abbrev shared_expr_Classification100_52 (c0_node c3_node : Int) : Prop := (((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
theorem normalization_8198 (c0_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification100_52 c0_node c3_node) := (iff_congr (normalization_8089 c0_node c3_node) (normalization_8197 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_6579 (c0_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2343 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8198 c0_node c3_node) hn

abbrev shared_expr_Classification100_53 (c0_node c3_node : Int) : Prop := ((((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2668 (c0_node c3_node : Int) : Prop := (shared_expr_Classification100_53 c0_node c3_node)

theorem normalized_2344 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8199 (c0_node c3_node : Int) : (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_8196 c0_node c3_node))

theorem normalization_8200 (c0_node c3_node : Int) : ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) := (or_congr (normalization_8091 c0_node c3_node) (normalization_8199 c0_node c3_node))

theorem normalization_8201 (c0_node c3_node : Int) : (¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) := (not_congr (normalization_8200 c0_node c3_node))

abbrev shared_expr_Classification100_54 (c0_node c3_node : Int) : Prop := (((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))))
theorem normalization_8202 (c0_node c3_node : Int) : (formula_2668 c0_node c3_node) ↔ (shared_expr_Classification100_54 c0_node c3_node) := (iff_congr (normalization_8197 c0_node c3_node) (normalization_8201 c0_node c3_node))

-- Checked replay of rewrite.
theorem replay_6580 (c0_node c3_node : Int) : (formula_2668 c0_node c3_node) := by
  classical
  have ht := (normalized_2344 (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8202 c0_node c3_node) hn

abbrev shared_expr_Classification100_55 (c0_node c3_node : Int) : Prop := (((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2669 (c0_node c3_node : Int) : Prop := (shared_expr_Classification100_55 c0_node c3_node)

theorem normalized_2345 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8203 (c0_node c3_node : Int) : (formula_2669 c0_node c3_node) ↔ (shared_expr_Classification100_54 c0_node c3_node) := (iff_congr (normalization_8089 c0_node c3_node) (normalization_8201 c0_node c3_node))

-- Checked replay of trans.
theorem replay_6581 (c0_node c3_node : Int) : (formula_2669 c0_node c3_node) := by
  classical
  have ht := (normalized_2345 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) (shared_expr_Classification100_54 c0_node c3_node))
  have n0 : (shared_expr_Classification100_52 c0_node c3_node) := by
    exact Iff.mp (normalization_8198 c0_node c3_node) (replay_6579 c0_node c3_node)
  have n1 : (shared_expr_Classification100_54 c0_node c3_node) := by
    exact Iff.mp (normalization_8202 c0_node c3_node) (replay_6580 c0_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8203 c0_node c3_node) hn

abbrev shared_expr_Classification100_56 (c0_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification100_57 (c0_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_2670 (c0_node c3_node c3_sign : Int) : Prop := ((shared_expr_Classification100_56 c0_node c3_node c3_sign) ∨ (shared_expr_Classification100_57 c0_node c3_node))

theorem normalized_2346 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_58 (c0_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification100_59 (c0_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_8204 (c0_node c3_node c3_sign : Int) : (formula_2670 c0_node c3_node c3_sign) ↔ ((shared_expr_Classification100_58 c0_node c3_node c3_sign) ∨ (shared_expr_Classification100_59 c0_node c3_node)) := (or_congr (and_congr (normalization_8201 c0_node c3_node) (normalization_6849 c3_sign)) (and_congr (not_congr (normalization_8201 c0_node c3_node)) (normalization_8091 c0_node c3_node)))

abbrev shared_expr_Classification100_60 (c0_node c3_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification100_61 (c0_node c3_node c3_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification100_60 c0_node c3_node))
theorem normalization_8205 (c0_node c3_node c3_sign : Int) : ((formula_2648 c0_node c3_node c3_sign) ↔ (formula_2670 c0_node c3_node c3_sign)) ↔ ((shared_expr_Classification100_61 c0_node c3_node c3_sign) ↔ ((shared_expr_Classification100_58 c0_node c3_node c3_sign) ∨ (shared_expr_Classification100_59 c0_node c3_node))) := (iff_congr (normalization_8092 c0_node c3_node c3_sign) (normalization_8204 c0_node c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_6582 (c0_node c3_node c3_sign : Int) : ((formula_2648 c0_node c3_node c3_sign) ↔ (formula_2670 c0_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2346 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification100_54 c0_node c3_node) := by
    exact Iff.mp (normalization_8203 c0_node c3_node) (replay_6581 c0_node c3_node)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6942 c3_sign) (replay_4980 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8205 c0_node c3_node c3_sign) hn

theorem normalized_2347 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_62 (c0_node c3_node : Int) : Prop := (((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_8206 (c0_node c3_node c3_sign : Int) : (formula_2620 c0_node c3_node c3_sign) ↔ ((shared_expr_Classification100_62 c0_node c3_node) ∨ (shared_expr_Classification100_58 c0_node c3_node c3_sign)) := (or_congr (and_congr (normalization_8200 c0_node c3_node) (normalization_8091 c0_node c3_node)) (and_congr (not_congr (normalization_8200 c0_node c3_node)) (normalization_6849 c3_sign)))

abbrev shared_expr_Classification100_63 (c0_node c3_node c3_sign : Int) : Prop := (((shared_expr_Classification100_58 c0_node c3_node c3_sign) ∨ (shared_expr_Classification100_59 c0_node c3_node)) ↔ ((shared_expr_Classification100_62 c0_node c3_node) ∨ (shared_expr_Classification100_58 c0_node c3_node c3_sign)))
theorem normalization_8207 (c0_node c3_node c3_sign : Int) : ((formula_2670 c0_node c3_node c3_sign) ↔ (formula_2620 c0_node c3_node c3_sign)) ↔ (shared_expr_Classification100_63 c0_node c3_node c3_sign) := (iff_congr (normalization_8204 c0_node c3_node c3_sign) (normalization_8206 c0_node c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_6583 (c0_node c3_node c3_sign : Int) : ((formula_2670 c0_node c3_node c3_sign) ↔ (formula_2620 c0_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2347 ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) (((c0_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8207 c0_node c3_node c3_sign) hn

theorem normalized_2348 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8208 (c0_node c3_node c3_sign : Int) : ((formula_2648 c0_node c3_node c3_sign) ↔ (formula_2620 c0_node c3_node c3_sign)) ↔ ((shared_expr_Classification100_61 c0_node c3_node c3_sign) ↔ ((shared_expr_Classification100_62 c0_node c3_node) ∨ (shared_expr_Classification100_58 c0_node c3_node c3_sign))) := (iff_congr (normalization_8092 c0_node c3_node c3_sign) (normalization_8206 c0_node c3_node c3_sign))

-- Checked replay of trans.
theorem replay_6584 (c0_node c3_node c3_sign : Int) : ((formula_2648 c0_node c3_node c3_sign) ↔ (formula_2620 c0_node c3_node c3_sign)) := by
  classical
  have ht := (normalized_2348 (shared_expr_Classification100_61 c0_node c3_node c3_sign) ((shared_expr_Classification100_58 c0_node c3_node c3_sign) ∨ (shared_expr_Classification100_59 c0_node c3_node)) ((shared_expr_Classification100_62 c0_node c3_node) ∨ (shared_expr_Classification100_58 c0_node c3_node c3_sign)))
  have n0 : ((shared_expr_Classification100_61 c0_node c3_node c3_sign) ↔ ((shared_expr_Classification100_58 c0_node c3_node c3_sign) ∨ (shared_expr_Classification100_59 c0_node c3_node))) := by
    exact Iff.mp (normalization_8205 c0_node c3_node c3_sign) (replay_6582 c0_node c3_node c3_sign)
  have n1 : (shared_expr_Classification100_63 c0_node c3_node c3_sign) := by
    exact Iff.mp (normalization_8207 c0_node c3_node c3_sign) (replay_6583 c0_node c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8208 c0_node c3_node c3_sign) hn

abbrev shared_expr_Classification100_64 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_2648 c0_node c3_node c3_sign)) ↔ (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_2620 c0_node c3_node c3_sign)))
abbrev formula_2671 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification100_64 c0_depth c0_node c3_depth c3_node c3_sign)

theorem normalized_2349 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification100_65 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ ((shared_expr_Classification100_62 c0_node c3_node) ∨ (shared_expr_Classification100_58 c0_node c3_node c3_sign)))
theorem normalization_8209 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ∨ (formula_2620 c0_node c3_node c3_sign)) ↔ (shared_expr_Classification100_65 c0_depth c0_node c3_depth c3_node c3_sign) := (or_congr (normalization_8188 c0_depth c3_depth) (normalization_8206 c0_node c3_node c3_sign))

abbrev shared_expr_Classification100_66 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification100_61 c0_node c3_node c3_sign)) ↔ (shared_expr_Classification100_65 c0_depth c0_node c3_depth c3_node c3_sign))
theorem normalization_8210 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (formula_2671 c0_depth c0_node c3_depth c3_node c3_sign) ↔ (shared_expr_Classification100_66 c0_depth c0_node c3_depth c3_node c3_sign) := (iff_congr (normalization_8093 c0_depth c0_node c3_depth c3_node c3_sign) (normalization_8209 c0_depth c0_node c3_depth c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_6585 (c0_depth c0_node c3_depth c3_node c3_sign : Int) : (formula_2671 c0_depth c0_node c3_depth c3_node c3_sign) := by
  classical
  have ht := (normalized_2349 (((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) (shared_expr_Classification100_61 c0_node c3_node c3_sign) ((shared_expr_Classification100_62 c0_node c3_node) ∨ (shared_expr_Classification100_58 c0_node c3_node c3_sign)))
  have n0 : (shared_expr_Classification100_51 c0_depth c3_depth) := by
    exact Iff.mp (normalization_8195 c0_depth c3_depth) (replay_6578 c0_depth c3_depth)
  have n1 : ((shared_expr_Classification100_61 c0_node c3_node c3_sign) ↔ ((shared_expr_Classification100_62 c0_node c3_node) ∨ (shared_expr_Classification100_58 c0_node c3_node c3_sign))) := by
    exact Iff.mp (normalization_8208 c0_node c3_node c3_sign) (replay_6584 c0_node c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8210 c0_depth c0_node c3_depth c3_node c3_sign) hn

end H4Formal.Generated.Classification
