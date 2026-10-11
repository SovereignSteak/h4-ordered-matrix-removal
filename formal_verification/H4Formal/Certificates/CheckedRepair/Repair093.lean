import H4Formal.Certificates.CheckedRepair.Repair092

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair093_0 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2286 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))))
abbrev formula_2313 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ∨ (shared_expr_Repair093_0 c2_group c2_level c2_mode c3_group c3_level c3_mode))

theorem normalized_2004 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair093_1 (c2_group c2_mode c3_group c3_mode : Int) : Prop := ((((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair093_2 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair093_1 c2_group c2_mode c3_group c3_mode)))
abbrev shared_expr_Repair093_3 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair093_2 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
theorem normalization_6920 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2313 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6902 c3_kind) (normalization_6918 c2_group c2_level c2_mode c3_group c3_level c3_mode))

abbrev shared_expr_Repair093_4 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (((((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair093_5 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair093_4 c2_group c2_mode c3_group c3_mode)) ∨ ((¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair093_6 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair093_5 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
abbrev shared_expr_Repair093_7 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_6 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem normalization_6921 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2304 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2313 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Repair093_7 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_6873 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (normalization_6920 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of monotonicity.
theorem replay_6111 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2304 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2313 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2004 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Repair093_6 c2_group c2_level c2_mode c3_group c3_level c3_mode) (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode))
  have n0 : ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_6909 c3_kind) (replay_6109 c3_kind)
  have n1 : ((shared_expr_Repair093_6 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := by
    exact Iff.mp (normalization_6919 c2_group c2_level c2_mode c3_group c3_level c3_mode) (replay_6110 c2_group c2_level c2_mode c3_group c3_level c3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6921 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2005 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6922 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2287 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6900 c3_kind) (or_congr (normalization_6901 c3_kind) (normalization_6918 c2_group c2_level c2_mode c3_group c3_level c3_mode)))

abbrev shared_expr_Repair093_8 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem normalization_6923 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2313 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2287 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Repair093_8 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_6920 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (normalization_6922 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of rewrite.
theorem replay_6112 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2313 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2287 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2005 ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)) (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode))
  have hn := ht
  exact Iff.mpr (normalization_6923 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2006 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair093_9 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_6 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem normalization_6924 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2304 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2287 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ↔ (shared_expr_Repair093_9 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := (iff_congr (normalization_6873 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (normalization_6922 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode))

-- Checked replay of trans.
theorem replay_6113 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((formula_2304 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ (formula_2287 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) := by
  classical
  have ht := (normalized_2006 ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_6 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair093_3 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
  have n0 : (shared_expr_Repair093_7 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_6921 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (replay_6111 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)
  have n1 : (shared_expr_Repair093_8 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := by
    exact Iff.mp (normalization_6923 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) (replay_6112 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6924 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) hn

theorem normalized_2007 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6925 (c3_kind : Int) : (c3_kind ≤ (1 : Int)) ↔ ((c3_kind) ≤ (1 : Int)) := by
  omega

theorem normalization_6926 (c3_kind : Int) : (c3_kind ≥ (1 : Int)) ↔ (¬ ((c3_kind) ≤ (0 : Int))) := by
  omega

theorem normalization_6927 (c3_kind : Int) : ((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int))) ↔ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) := (and_congr (normalization_6925 c3_kind) (normalization_6926 c3_kind))

theorem normalization_6928 (c3_kind : Int) : ((c3_kind = (1 : Int)) ↔ ((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int)))) ↔ ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) := (iff_congr (normalization_6804 c3_kind) (normalization_6927 c3_kind))

-- Checked replay of rewrite.
theorem replay_6114 (c3_kind : Int) : ((c3_kind = (1 : Int)) ↔ ((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2007 (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6928 c3_kind) hn

theorem normalized_2008 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6929 (c3_kind : Int) : (¬ (c3_kind ≤ (1 : Int))) ↔ (¬ ((c3_kind) ≤ (1 : Int))) := (not_congr (normalization_6925 c3_kind))

theorem normalization_6930 (c3_kind : Int) : (¬ (c3_kind ≥ (1 : Int))) ↔ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) := (not_congr (normalization_6926 c3_kind))

theorem normalization_6931 (c3_kind : Int) : ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))) ↔ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) := (or_congr (normalization_6929 c3_kind) (normalization_6930 c3_kind))

theorem normalization_6932 (c3_kind : Int) : (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))))) := (not_congr (normalization_6931 c3_kind))

theorem normalization_6933 (c3_kind : Int) : (((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) ↔ ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_6927 c3_kind) (normalization_6932 c3_kind))

-- Checked replay of rewrite.
theorem replay_6115 (c3_kind : Int) : (((c3_kind ≤ (1 : Int)) ∧ (c3_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2008 ((c3_kind) ≤ (1 : Int)) ((c3_kind) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6933 c3_kind) hn

theorem normalized_2009 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6934 (c3_kind : Int) : ((c3_kind = (1 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) ↔ ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_6804 c3_kind) (normalization_6932 c3_kind))

-- Checked replay of trans.
theorem replay_6116 (c3_kind : Int) : ((c3_kind = (1 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2009 (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))))
  have n0 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_6928 c3_kind) (replay_6114 c3_kind)
  have n1 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6933 c3_kind) (replay_6115 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6934 c3_kind) hn

theorem normalized_2010 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6935 (c3_kind : Int) : (c3_kind ≤ (2 : Int)) ↔ ((c3_kind) ≤ (2 : Int)) := by
  omega

theorem normalization_6936 (c3_kind : Int) : (c3_kind ≥ (2 : Int)) ↔ (¬ ((c3_kind) ≤ (1 : Int))) := by
  omega

theorem normalization_6937 (c3_kind : Int) : ((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int))) ↔ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) := (and_congr (normalization_6935 c3_kind) (normalization_6936 c3_kind))

theorem normalization_6938 (c3_kind : Int) : ((c3_kind = (2 : Int)) ↔ ((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int)))) ↔ ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) := (iff_congr (normalization_6806 c3_kind) (normalization_6937 c3_kind))

-- Checked replay of rewrite.
theorem replay_6117 (c3_kind : Int) : ((c3_kind = (2 : Int)) ↔ ((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_2010 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6938 c3_kind) hn

theorem normalized_2011 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6939 (c3_kind : Int) : (¬ (c3_kind ≤ (2 : Int))) ↔ (¬ ((c3_kind) ≤ (2 : Int))) := (not_congr (normalization_6935 c3_kind))

theorem normalization_6940 (c3_kind : Int) : (¬ (c3_kind ≥ (2 : Int))) ↔ (¬ (¬ ((c3_kind) ≤ (1 : Int)))) := (not_congr (normalization_6936 c3_kind))

theorem normalization_6941 (c3_kind : Int) : ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) := (or_congr (normalization_6939 c3_kind) (normalization_6940 c3_kind))

theorem normalization_6942 (c3_kind : Int) : (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := (not_congr (normalization_6941 c3_kind))

theorem normalization_6943 (c3_kind : Int) : (((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_6937 c3_kind) (normalization_6942 c3_kind))

-- Checked replay of rewrite.
theorem replay_6118 (c3_kind : Int) : (((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_2011 ((c3_kind) ≤ (2 : Int)) ((c3_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6943 c3_kind) hn

theorem normalized_2012 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6944 (c3_kind : Int) : ((c3_kind = (2 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_6806 c3_kind) (normalization_6942 c3_kind))

-- Checked replay of trans.
theorem replay_6119 (c3_kind : Int) : ((c3_kind = (2 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_2012 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
  have n0 : ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_6938 c3_kind) (replay_6117 c3_kind)
  have n1 : ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6943 c3_kind) (replay_6118 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6944 c3_kind) hn

theorem normalized_2013 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6945 (c3_kind : Int) : (¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := (not_congr (normalization_6942 c3_kind))

theorem normalization_6946 (c3_kind : Int) : ((¬ (c3_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))))) ↔ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))))) := (iff_congr (normalization_6842 c3_kind) (normalization_6945 c3_kind))

-- Checked replay of monotonicity.
theorem replay_6120 (c3_kind : Int) : ((¬ (c3_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_2013 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))
  have n0 : ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6944 c3_kind) (replay_6119 c3_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_6946 c3_kind) hn

theorem normalized_2014 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6947 (c3_kind : Int) : ((¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ↔ ((¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_6945 c3_kind) (normalization_6941 c3_kind))

-- Checked replay of rewrite.
theorem replay_6121 (c3_kind : Int) : ((¬ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_2014 ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_6947 c3_kind) hn

theorem normalized_2015 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6948 (c3_kind : Int) : ((¬ (c3_kind = (2 : Int))) ↔ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ↔ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_6842 c3_kind) (normalization_6941 c3_kind))

-- Checked replay of trans.
theorem replay_6122 (c3_kind : Int) : ((¬ (c3_kind = (2 : Int))) ↔ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_2015 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))
  have n0 : ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_6946 c3_kind) (replay_6120 c3_kind)
  have n1 : ((¬ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_6947 c3_kind) (replay_6121 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6948 c3_kind) hn

theorem normalized_2016 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6949 (c2_depth c3_depth : Int) : (c2_depth ≤ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6950 (c2_depth c3_depth : Int) : (c2_depth ≥ c3_depth) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6951 (c2_depth c3_depth : Int) : ((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_6949 c2_depth c3_depth) (normalization_6950 c2_depth c3_depth))

abbrev shared_expr_Repair093_10 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
theorem normalization_6952 (c2_depth c3_depth : Int) : ((c2_depth = c3_depth) ↔ ((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth))) ↔ (shared_expr_Repair093_10 c2_depth c3_depth) := (iff_congr (normalization_6807 c2_depth c3_depth) (normalization_6951 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6123 (c2_depth c3_depth : Int) : ((c2_depth = c3_depth) ↔ ((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth))) := by
  classical
  have ht := (normalized_2016 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6952 c2_depth c3_depth) hn

theorem normalized_2017 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6953 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6954 (c2_depth c3_depth : Int) : ((c2_depth ≤ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := (iff_congr (normalization_6949 c2_depth c3_depth) (normalization_6953 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6124 (c2_depth c3_depth : Int) : ((c2_depth ≤ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2017 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6954 c2_depth c3_depth) hn

theorem normalized_2018 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6955 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6956 (c2_depth c3_depth : Int) : ((c2_depth ≥ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_6950 c2_depth c3_depth) (normalization_6955 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6125 (c2_depth c3_depth : Int) : ((c2_depth ≥ c3_depth) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2018 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6956 c2_depth c3_depth) hn

theorem normalized_2019 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6957 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_6953 c2_depth c3_depth) (normalization_6955 c2_depth c3_depth))

theorem normalization_6958 (c2_depth c3_depth : Int) : (((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Repair093_10 c2_depth c3_depth) := (iff_congr (normalization_6951 c2_depth c3_depth) (normalization_6957 c2_depth c3_depth))

-- Checked replay of monotonicity.
theorem replay_6126 (c2_depth c3_depth : Int) : (((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2019 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))
  have n0 : (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6954 c2_depth c3_depth) (replay_6124 c2_depth c3_depth)
  have n1 : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6956 c2_depth c3_depth) (replay_6125 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6958 c2_depth c3_depth) hn

abbrev shared_expr_Repair093_11 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))))
abbrev formula_2314 (c2_depth c3_depth : Int) : Prop := (shared_expr_Repair093_11 c2_depth c3_depth)

theorem normalized_2020 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6959 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := (not_congr (normalization_6953 c2_depth c3_depth))

theorem normalization_6960 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_6955 c2_depth c3_depth))

theorem normalization_6961 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_6959 c2_depth c3_depth) (normalization_6960 c2_depth c3_depth))

theorem normalization_6962 (c2_depth c3_depth : Int) : (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_6961 c2_depth c3_depth))

abbrev shared_expr_Repair093_12 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))))))
theorem normalization_6963 (c2_depth c3_depth : Int) : (formula_2314 c2_depth c3_depth) ↔ (shared_expr_Repair093_12 c2_depth c3_depth) := (iff_congr (normalization_6957 c2_depth c3_depth) (normalization_6962 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6127 (c2_depth c3_depth : Int) : (formula_2314 c2_depth c3_depth) := by
  classical
  have ht := (normalized_2020 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6963 c2_depth c3_depth) hn

theorem normalized_2021 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6964 (c2_depth c3_depth : Int) : (((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair093_12 c2_depth c3_depth) := (iff_congr (normalization_6951 c2_depth c3_depth) (normalization_6962 c2_depth c3_depth))

-- Checked replay of trans.
theorem replay_6128 (c2_depth c3_depth : Int) : (((c2_depth ≤ c3_depth) ∧ (c2_depth ≥ c3_depth)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2021 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Repair093_12 c2_depth c3_depth))
  have n0 : (shared_expr_Repair093_10 c2_depth c3_depth) := by
    exact Iff.mp (normalization_6958 c2_depth c3_depth) (replay_6126 c2_depth c3_depth)
  have n1 : (shared_expr_Repair093_12 c2_depth c3_depth) := by
    exact Iff.mp (normalization_6963 c2_depth c3_depth) (replay_6127 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6964 c2_depth c3_depth) hn

theorem normalized_2022 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6965 (c2_depth c3_depth : Int) : ((c2_depth = c3_depth) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair093_12 c2_depth c3_depth) := (iff_congr (normalization_6807 c2_depth c3_depth) (normalization_6962 c2_depth c3_depth))

-- Checked replay of trans.
theorem replay_6129 (c2_depth c3_depth : Int) : ((c2_depth = c3_depth) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2022 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Repair093_12 c2_depth c3_depth))
  have n0 : (shared_expr_Repair093_10 c2_depth c3_depth) := by
    exact Iff.mp (normalization_6952 c2_depth c3_depth) (replay_6123 c2_depth c3_depth)
  have n1 : (shared_expr_Repair093_12 c2_depth c3_depth) := by
    exact Iff.mp (normalization_6964 c2_depth c3_depth) (replay_6128 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6965 c2_depth c3_depth) hn

theorem normalized_2023 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6966 (c2_node c3_node : Int) : (c2_node ≤ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_6967 (c2_node c3_node : Int) : (c2_node ≥ c3_node) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6968 (c2_node c3_node : Int) : ((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_6966 c2_node c3_node) (normalization_6967 c2_node c3_node))

abbrev shared_expr_Repair093_13 (c2_node c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
theorem normalization_6969 (c2_node c3_node : Int) : ((c2_node = c3_node) ↔ ((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node))) ↔ (shared_expr_Repair093_13 c2_node c3_node) := (iff_congr (normalization_6808 c2_node c3_node) (normalization_6968 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_6130 (c2_node c3_node : Int) : ((c2_node = c3_node) ↔ ((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node))) := by
  classical
  have ht := (normalized_2023 (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6969 c2_node c3_node) hn

theorem normalized_2024 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6970 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_6971 (c2_node c3_node : Int) : ((c2_node ≤ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (iff_congr (normalization_6966 c2_node c3_node) (normalization_6970 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_6131 (c2_node c3_node : Int) : ((c2_node ≤ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2024 ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6971 c2_node c3_node) hn

theorem normalized_2025 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6972 (c2_node c3_node : Int) : ((c2_node ≥ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_6967 c2_node c3_node) (normalization_6874 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_6132 (c2_node c3_node : Int) : ((c2_node ≥ c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2025 ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6972 c2_node c3_node) hn

theorem normalized_2026 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6973 (c2_node c3_node : Int) : (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_6970 c2_node c3_node) (normalization_6874 c2_node c3_node))

theorem normalization_6974 (c2_node c3_node : Int) : (((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair093_13 c2_node c3_node) := (iff_congr (normalization_6968 c2_node c3_node) (normalization_6973 c2_node c3_node))

-- Checked replay of monotonicity.
theorem replay_6133 (c2_node c3_node : Int) : (((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2026 ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
  have n0 : (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6971 c2_node c3_node) (replay_6131 c2_node c3_node)
  have n1 : ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6972 c2_node c3_node) (replay_6132 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6974 c2_node c3_node) hn

abbrev shared_expr_Repair093_14 (c2_node c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))))
abbrev formula_2315 (c2_node c3_node : Int) : Prop := (shared_expr_Repair093_14 c2_node c3_node)

theorem normalized_2027 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6975 (c2_node c3_node : Int) : (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_6970 c2_node c3_node))

theorem normalization_6976 (c2_node c3_node : Int) : ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_6975 c2_node c3_node) (normalization_6875 c2_node c3_node))

theorem normalization_6977 (c2_node c3_node : Int) : (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_6976 c2_node c3_node))

abbrev shared_expr_Repair093_15 (c2_node c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))))
theorem normalization_6978 (c2_node c3_node : Int) : (formula_2315 c2_node c3_node) ↔ (shared_expr_Repair093_15 c2_node c3_node) := (iff_congr (normalization_6973 c2_node c3_node) (normalization_6977 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_6134 (c2_node c3_node : Int) : (formula_2315 c2_node c3_node) := by
  classical
  have ht := (normalized_2027 ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6978 c2_node c3_node) hn

theorem normalized_2028 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6979 (c2_node c3_node : Int) : (((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair093_15 c2_node c3_node) := (iff_congr (normalization_6968 c2_node c3_node) (normalization_6977 c2_node c3_node))

-- Checked replay of trans.
theorem replay_6135 (c2_node c3_node : Int) : (((c2_node ≤ c3_node) ∧ (c2_node ≥ c3_node)) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2028 (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Repair093_15 c2_node c3_node))
  have n0 : (shared_expr_Repair093_13 c2_node c3_node) := by
    exact Iff.mp (normalization_6974 c2_node c3_node) (replay_6133 c2_node c3_node)
  have n1 : (shared_expr_Repair093_15 c2_node c3_node) := by
    exact Iff.mp (normalization_6978 c2_node c3_node) (replay_6134 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6979 c2_node c3_node) hn

theorem normalized_2029 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6980 (c2_node c3_node : Int) : ((c2_node = c3_node) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair093_15 c2_node c3_node) := (iff_congr (normalization_6808 c2_node c3_node) (normalization_6977 c2_node c3_node))

-- Checked replay of trans.
theorem replay_6136 (c2_node c3_node : Int) : ((c2_node = c3_node) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2029 (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) (shared_expr_Repair093_15 c2_node c3_node))
  have n0 : (shared_expr_Repair093_13 c2_node c3_node) := by
    exact Iff.mp (normalization_6969 c2_node c3_node) (replay_6130 c2_node c3_node)
  have n1 : (shared_expr_Repair093_15 c2_node c3_node) := by
    exact Iff.mp (normalization_6979 c2_node c3_node) (replay_6135 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6980 c2_node c3_node) hn

theorem normalized_2030 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6981 (c2_sign : Int) : ((c2_sign ≤ (0 : Int)) ∧ (c2_sign ≥ (0 : Int))) ↔ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) := (and_congr (normalization_72 c2_sign) (normalization_74 c2_sign))

theorem normalization_6982 (c2_sign : Int) : ((c2_sign = (0 : Int)) ↔ ((c2_sign ≤ (0 : Int)) ∧ (c2_sign ≥ (0 : Int)))) ↔ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int))))) := (iff_congr (normalization_10 c2_sign) (normalization_6981 c2_sign))

-- Checked replay of rewrite.
theorem replay_6137 (c2_sign : Int) : ((c2_sign = (0 : Int)) ↔ ((c2_sign ≤ (0 : Int)) ∧ (c2_sign ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2030 (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6982 c2_sign) hn

theorem normalized_2031 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6983 (c2_sign : Int) : (((c2_sign ≤ (0 : Int)) ∧ (c2_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))))) ↔ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_6981 c2_sign) (normalization_113 c2_sign))

-- Checked replay of rewrite.
theorem replay_6138 (c2_sign : Int) : (((c2_sign ≤ (0 : Int)) ∧ (c2_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2031 ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6983 c2_sign) hn

theorem normalized_2032 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6984 (c2_sign : Int) : ((c2_sign = (0 : Int)) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))))) ↔ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_10 c2_sign) (normalization_113 c2_sign))

-- Checked replay of trans.
theorem replay_6139 (c2_sign : Int) : ((c2_sign = (0 : Int)) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2032 (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))))
  have n0 : ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_6982 c2_sign) (replay_6137 c2_sign)
  have n1 : ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6983 c2_sign) (replay_6138 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6984 c2_sign) hn

theorem normalized_2033 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6985 (c3_sign : Int) : (c3_sign ≤ (1 : Int)) ↔ ((c3_sign) ≤ (1 : Int)) := by
  omega

theorem normalization_6986 (c3_sign : Int) : (c3_sign ≥ (1 : Int)) ↔ (¬ ((c3_sign) ≤ (0 : Int))) := by
  omega

theorem normalization_6987 (c3_sign : Int) : ((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int))) ↔ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) := (and_congr (normalization_6985 c3_sign) (normalization_6986 c3_sign))

theorem normalization_6988 (c3_sign : Int) : ((c3_sign = (1 : Int)) ↔ ((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int)))) ↔ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) := (iff_congr (normalization_6809 c3_sign) (normalization_6987 c3_sign))

-- Checked replay of rewrite.
theorem replay_6140 (c3_sign : Int) : ((c3_sign = (1 : Int)) ↔ ((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2033 (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6988 c3_sign) hn

theorem normalized_2034 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6989 (c3_sign : Int) : (¬ (c3_sign ≤ (1 : Int))) ↔ (¬ ((c3_sign) ≤ (1 : Int))) := (not_congr (normalization_6985 c3_sign))

theorem normalization_6990 (c3_sign : Int) : (¬ (c3_sign ≥ (1 : Int))) ↔ (¬ (¬ ((c3_sign) ≤ (0 : Int)))) := (not_congr (normalization_6986 c3_sign))

theorem normalization_6991 (c3_sign : Int) : ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ↔ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) := (or_congr (normalization_6989 c3_sign) (normalization_6990 c3_sign))

theorem normalization_6992 (c3_sign : Int) : (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_6991 c3_sign))

theorem normalization_6993 (c3_sign : Int) : (((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int))) ↔ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_6987 c3_sign) (normalization_6992 c3_sign))

-- Checked replay of rewrite.
theorem replay_6141 (c3_sign : Int) : (((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int))) ↔ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2034 ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6993 c3_sign) hn

theorem normalized_2035 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6994 (c3_sign : Int) : ((c3_sign = (1 : Int)) ↔ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_6809 c3_sign) (normalization_6992 c3_sign))

-- Checked replay of trans.
theorem replay_6142 (c3_sign : Int) : ((c3_sign = (1 : Int)) ↔ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2035 (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))))
  have n0 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_6988 c3_sign) (replay_6140 c3_sign)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6993 c3_sign) (replay_6141 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6994 c3_sign) hn

theorem normalized_2036 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6995 (c2_sign c3_sign : Int) : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (and_congr (normalization_113 c2_sign) (normalization_6992 c3_sign))

abbrev shared_expr_Repair093_16 (c2_sign c3_sign : Int) : Prop := (((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))))
theorem normalization_6996 (c2_sign c3_sign : Int) : (((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) ↔ (shared_expr_Repair093_16 c2_sign c3_sign) := (iff_congr (normalization_6810 c2_sign c3_sign) (normalization_6995 c2_sign c3_sign))

-- Checked replay of monotonicity.
theorem replay_6143 (c2_sign c3_sign : Int) : (((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_2036 (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6984 c2_sign) (replay_6139 c2_sign)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6994 c3_sign) (replay_6142 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6996 c2_sign c3_sign) hn

abbrev shared_expr_Repair093_17 (c2_sign c3_sign : Int) : Prop := (((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev formula_2316 (c2_sign c3_sign : Int) : Prop := (shared_expr_Repair093_17 c2_sign c3_sign)

theorem normalized_2037 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6997 (c2_sign c3_sign : Int) : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ↔ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) := (or_congr (normalization_73 c2_sign) (or_congr (normalization_75 c2_sign) (or_congr (normalization_6989 c3_sign) (normalization_6990 c3_sign))))

theorem normalization_6998 (c2_sign c3_sign : Int) : (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_6997 c2_sign c3_sign))

abbrev shared_expr_Repair093_18 (c2_sign c3_sign : Int) : Prop := (((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_6999 (c2_sign c3_sign : Int) : (formula_2316 c2_sign c3_sign) ↔ (shared_expr_Repair093_18 c2_sign c3_sign) := (iff_congr (normalization_6995 c2_sign c3_sign) (normalization_6998 c2_sign c3_sign))

-- Checked replay of rewrite.
theorem replay_6144 (c2_sign c3_sign : Int) : (formula_2316 c2_sign c3_sign) := by
  classical
  have ht := (normalized_2037 ((c2_sign) ≤ (0 : Int)) ((c2_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6999 c2_sign c3_sign) hn

theorem normalized_2038 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair093_19 (c2_sign c3_sign : Int) : Prop := (((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
theorem normalization_7000 (c2_sign c3_sign : Int) : (((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ (shared_expr_Repair093_19 c2_sign c3_sign) := (iff_congr (normalization_6810 c2_sign c3_sign) (normalization_6998 c2_sign c3_sign))

-- Checked replay of trans.
theorem replay_6145 (c2_sign c3_sign : Int) : (((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2038 ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair093_16 c2_sign c3_sign) := by
    exact Iff.mp (normalization_6996 c2_sign c3_sign) (replay_6143 c2_sign c3_sign)
  have n1 : (shared_expr_Repair093_18 c2_sign c3_sign) := by
    exact Iff.mp (normalization_6999 c2_sign c3_sign) (replay_6144 c2_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7000 c2_sign c3_sign) hn

abbrev shared_expr_Repair093_20 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair093_21 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Repair093_20 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))
abbrev formula_2317 (c2_node c2_sign c3_node c3_sign : Int) : Prop := (shared_expr_Repair093_21 c2_node c2_sign c3_node c3_sign)

abbrev shared_expr_Repair093_22 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_2317 c2_node c2_sign c3_node c3_sign))
abbrev formula_2318 (c2_node c2_sign c3_node c3_sign : Int) : Prop := (shared_expr_Repair093_22 c2_node c2_sign c3_node c3_sign)

theorem normalized_2039 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair093_23 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair093_24 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Repair093_23 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_7001 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2317 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Repair093_24 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_6977 c2_node c3_node) (normalization_6998 c2_sign c3_sign)) (and_congr (not_congr (normalization_6977 c2_node c3_node)) (normalization_6875 c2_node c3_node)))

abbrev shared_expr_Repair093_25 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair093_26 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Repair093_25 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_7002 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2318 c2_node c2_sign c3_node c3_sign) ↔ ((shared_expr_Repair093_26 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Repair093_24 c2_node c2_sign c3_node c3_sign)) := (iff_congr (normalization_6876 c2_node c2_sign c3_node c3_sign) (normalization_7001 c2_node c2_sign c3_node c3_sign))

-- Checked replay of monotonicity.
theorem replay_6146 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2318 c2_node c2_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_2039 (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair093_15 c2_node c3_node) := by
    exact Iff.mp (normalization_6980 c2_node c3_node) (replay_6136 c2_node c3_node)
  have n1 : (shared_expr_Repair093_19 c2_sign c3_sign) := by
    exact Iff.mp (normalization_7000 c2_sign c3_sign) (replay_6145 c2_sign c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7002 c2_node c2_sign c3_node c3_sign) hn

theorem normalized_2040 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair093_27 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_23 c2_node c2_sign c3_node c3_sign))
theorem normalization_7003 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2281 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Repair093_27 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_6976 c2_node c3_node) (normalization_6875 c2_node c3_node)) (and_congr (not_congr (normalization_6976 c2_node c3_node)) (normalization_6998 c2_sign c3_sign)))

theorem normalization_7004 (c2_node c2_sign c3_node c3_sign : Int) : ((formula_2317 c2_node c2_sign c3_node c3_sign) ↔ (formula_2281 c2_node c2_sign c3_node c3_sign)) ↔ ((shared_expr_Repair093_24 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Repair093_27 c2_node c2_sign c3_node c3_sign)) := (iff_congr (normalization_7001 c2_node c2_sign c3_node c3_sign) (normalization_7003 c2_node c2_sign c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_6147 (c2_node c2_sign c3_node c3_sign : Int) : ((formula_2317 c2_node c2_sign c3_node c3_sign) ↔ (formula_2281 c2_node c2_sign c3_node c3_sign)) := by
  classical
  have ht := (normalized_2040 ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7004 c2_node c2_sign c3_node c3_sign) hn

abbrev shared_expr_Repair093_28 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (formula_2281 c2_node c2_sign c3_node c3_sign))
abbrev formula_2319 (c2_node c2_sign c3_node c3_sign : Int) : Prop := (shared_expr_Repair093_28 c2_node c2_sign c3_node c3_sign)

theorem normalized_2041 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7005 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2319 c2_node c2_sign c3_node c3_sign) ↔ ((shared_expr_Repair093_26 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Repair093_27 c2_node c2_sign c3_node c3_sign)) := (iff_congr (normalization_6876 c2_node c2_sign c3_node c3_sign) (normalization_7003 c2_node c2_sign c3_node c3_sign))

-- Checked replay of trans.
theorem replay_6148 (c2_node c2_sign c3_node c3_sign : Int) : (formula_2319 c2_node c2_sign c3_node c3_sign) := by
  classical
  have ht := (normalized_2041 (shared_expr_Repair093_26 c2_node c2_sign c3_node c3_sign) (shared_expr_Repair093_24 c2_node c2_sign c3_node c3_sign) (shared_expr_Repair093_27 c2_node c2_sign c3_node c3_sign))
  have n0 : ((shared_expr_Repair093_26 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Repair093_24 c2_node c2_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_7002 c2_node c2_sign c3_node c3_sign) (replay_6146 c2_node c2_sign c3_node c3_sign)
  have n1 : ((shared_expr_Repair093_24 c2_node c2_sign c3_node c3_sign) ↔ (shared_expr_Repair093_27 c2_node c2_sign c3_node c3_sign)) := by
    exact Iff.mp (normalization_7004 c2_node c2_sign c3_node c3_sign) (replay_6147 c2_node c2_sign c3_node c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7005 c2_node c2_sign c3_node c3_sign) hn

theorem normalized_2042 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7006 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_7007 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_7008 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_7006 c2_depth c3_depth) (normalization_7007 c2_depth c3_depth))

abbrev shared_expr_Repair093_29 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
theorem normalization_7009 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Repair093_29 c2_depth c3_depth) := (iff_congr (normalization_6877 c2_depth c3_depth) (normalization_7008 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6149 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_2042 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7009 c2_depth c3_depth) hn

abbrev shared_expr_Repair093_30 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))))
abbrev formula_2320 (c2_depth c3_depth : Int) : Prop := (shared_expr_Repair093_30 c2_depth c3_depth)

theorem normalized_2043 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7010 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) := (not_congr (normalization_7006 c2_depth c3_depth))

theorem normalization_7011 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_7007 c2_depth c3_depth))

theorem normalization_7012 (c2_depth c3_depth : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_7010 c2_depth c3_depth) (normalization_7011 c2_depth c3_depth))

theorem normalization_7013 (c2_depth c3_depth : Int) : (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_7012 c2_depth c3_depth))

abbrev shared_expr_Repair093_31 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))))))
theorem normalization_7014 (c2_depth c3_depth : Int) : (formula_2320 c2_depth c3_depth) ↔ (shared_expr_Repair093_31 c2_depth c3_depth) := (iff_congr (normalization_7008 c2_depth c3_depth) (normalization_7013 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6150 (c2_depth c3_depth : Int) : (formula_2320 c2_depth c3_depth) := by
  classical
  have ht := (normalized_2043 ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7014 c2_depth c3_depth) hn

theorem normalized_2044 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7015 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Repair093_31 c2_depth c3_depth) := (iff_congr (normalization_6877 c2_depth c3_depth) (normalization_7013 c2_depth c3_depth))

-- Checked replay of trans.
theorem replay_6151 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_2044 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Repair093_31 c2_depth c3_depth))
  have n0 : (shared_expr_Repair093_29 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7009 c2_depth c3_depth) (replay_6149 c2_depth c3_depth)
  have n1 : (shared_expr_Repair093_31 c2_depth c3_depth) := by
    exact Iff.mp (normalization_7014 c2_depth c3_depth) (replay_6150 c2_depth c3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7015 c2_depth c3_depth) hn

theorem normalized_2045 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7016 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7017 (c2_node c3_node : Int) : (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (and_congr (normalization_7016 c2_node c3_node) (normalization_6879 c2_node c3_node))

abbrev shared_expr_Repair093_32 (c2_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_7018 (c2_node c3_node : Int) : (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Repair093_32 c2_node c3_node) := (iff_congr (normalization_6878 c2_node c3_node) (normalization_7017 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_6152 (c2_node c3_node : Int) : (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2045 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_7018 c2_node c3_node) hn

abbrev shared_expr_Repair093_33 (c2_node c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2321 (c2_node c3_node : Int) : Prop := (shared_expr_Repair093_33 c2_node c3_node)

theorem normalized_2046 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7019 (c2_node c3_node : Int) : (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7016 c2_node c3_node))

theorem normalization_7020 (c2_node c3_node : Int) : ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) := (or_congr (normalization_7019 c2_node c3_node) (normalization_6880 c2_node c3_node))

theorem normalization_7021 (c2_node c3_node : Int) : (¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) := (not_congr (normalization_7020 c2_node c3_node))

abbrev shared_expr_Repair093_34 (c2_node c3_node : Int) : Prop := (((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))))
theorem normalization_7022 (c2_node c3_node : Int) : (formula_2321 c2_node c3_node) ↔ (shared_expr_Repair093_34 c2_node c3_node) := (iff_congr (normalization_7017 c2_node c3_node) (normalization_7021 c2_node c3_node))

-- Checked replay of rewrite.
theorem replay_6153 (c2_node c3_node : Int) : (formula_2321 c2_node c3_node) := by
  classical
  have ht := (normalized_2046 (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7022 c2_node c3_node) hn

abbrev shared_expr_Repair093_35 (c2_node c3_node : Int) : Prop := (((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_2322 (c2_node c3_node : Int) : Prop := (shared_expr_Repair093_35 c2_node c3_node)

theorem normalized_2047 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7023 (c2_node c3_node : Int) : (formula_2322 c2_node c3_node) ↔ (shared_expr_Repair093_34 c2_node c3_node) := (iff_congr (normalization_6878 c2_node c3_node) (normalization_7021 c2_node c3_node))

-- Checked replay of trans.
theorem replay_6154 (c2_node c3_node : Int) : (formula_2322 c2_node c3_node) := by
  classical
  have ht := (normalized_2047 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) (shared_expr_Repair093_34 c2_node c3_node))
  have n0 : (shared_expr_Repair093_32 c2_node c3_node) := by
    exact Iff.mp (normalization_7018 c2_node c3_node) (replay_6152 c2_node c3_node)
  have n1 : (shared_expr_Repair093_34 c2_node c3_node) := by
    exact Iff.mp (normalization_7022 c2_node c3_node) (replay_6153 c2_node c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7023 c2_node c3_node) hn

abbrev shared_expr_Repair093_36 (c2_node c2_sign c3_node : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))))
abbrev shared_expr_Repair093_37 (c2_node c3_node : Int) : Prop := ((¬ (¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2323 (c2_node c2_sign c3_node : Int) : Prop := ((shared_expr_Repair093_36 c2_node c2_sign c3_node) ∨ (shared_expr_Repair093_37 c2_node c3_node))

theorem normalized_2048 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair093_38 (c2_node c2_sign c3_node : Int) : Prop := ((¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Repair093_39 (c2_node c3_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_7024 (c2_node c2_sign c3_node : Int) : (formula_2323 c2_node c2_sign c3_node) ↔ ((shared_expr_Repair093_38 c2_node c2_sign c3_node) ∨ (shared_expr_Repair093_39 c2_node c3_node)) := (or_congr (and_congr (normalization_7021 c2_node c3_node) (normalization_113 c2_sign)) (and_congr (not_congr (normalization_7021 c2_node c3_node)) (normalization_6880 c2_node c3_node)))

abbrev shared_expr_Repair093_40 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair093_41 (c2_node c2_sign c3_node : Int) : Prop := ((((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair093_40 c2_node c3_node))
theorem normalization_7025 (c2_node c2_sign c3_node : Int) : ((formula_2305 c2_node c2_sign c3_node) ↔ (formula_2323 c2_node c2_sign c3_node)) ↔ ((shared_expr_Repair093_41 c2_node c2_sign c3_node) ↔ ((shared_expr_Repair093_38 c2_node c2_sign c3_node) ∨ (shared_expr_Repair093_39 c2_node c3_node))) := (iff_congr (normalization_6881 c2_node c2_sign c3_node) (normalization_7024 c2_node c2_sign c3_node))

-- Checked replay of monotonicity.
theorem replay_6155 (c2_node c2_sign c3_node : Int) : ((formula_2305 c2_node c2_sign c3_node) ↔ (formula_2323 c2_node c2_sign c3_node)) := by
  classical
  have ht := (normalized_2048 ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Repair093_34 c2_node c3_node) := by
    exact Iff.mp (normalization_7023 c2_node c3_node) (replay_6154 c2_node c3_node)
  have n1 : ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6984 c2_sign) (replay_6139 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7025 c2_node c2_sign c3_node) hn

theorem normalized_2049 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair093_42 (c2_node c3_node : Int) : Prop := (((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
theorem normalization_7026 (c2_node c2_sign c3_node : Int) : (formula_2279 c2_node c2_sign c3_node) ↔ ((shared_expr_Repair093_42 c2_node c3_node) ∨ (shared_expr_Repair093_38 c2_node c2_sign c3_node)) := (or_congr (and_congr (normalization_7020 c2_node c3_node) (normalization_6880 c2_node c3_node)) (and_congr (not_congr (normalization_7020 c2_node c3_node)) (normalization_113 c2_sign)))

theorem normalization_7027 (c2_node c2_sign c3_node : Int) : ((formula_2323 c2_node c2_sign c3_node) ↔ (formula_2279 c2_node c2_sign c3_node)) ↔ (((shared_expr_Repair093_38 c2_node c2_sign c3_node) ∨ (shared_expr_Repair093_39 c2_node c3_node)) ↔ ((shared_expr_Repair093_42 c2_node c3_node) ∨ (shared_expr_Repair093_38 c2_node c2_sign c3_node))) := (iff_congr (normalization_7024 c2_node c2_sign c3_node) (normalization_7026 c2_node c2_sign c3_node))

-- Checked replay of rewrite.
theorem replay_6156 (c2_node c2_sign c3_node : Int) : ((formula_2323 c2_node c2_sign c3_node) ↔ (formula_2279 c2_node c2_sign c3_node)) := by
  classical
  have ht := (normalized_2049 ((¬ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∨ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (-1 : Int))))) (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7027 c2_node c2_sign c3_node) hn

theorem normalized_2050 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7028 (c2_node c2_sign c3_node : Int) : ((formula_2305 c2_node c2_sign c3_node) ↔ (formula_2279 c2_node c2_sign c3_node)) ↔ ((shared_expr_Repair093_41 c2_node c2_sign c3_node) ↔ ((shared_expr_Repair093_42 c2_node c3_node) ∨ (shared_expr_Repair093_38 c2_node c2_sign c3_node))) := (iff_congr (normalization_6881 c2_node c2_sign c3_node) (normalization_7026 c2_node c2_sign c3_node))

-- Checked replay of trans.
theorem replay_6157 (c2_node c2_sign c3_node : Int) : ((formula_2305 c2_node c2_sign c3_node) ↔ (formula_2279 c2_node c2_sign c3_node)) := by
  classical
  have ht := (normalized_2050 (shared_expr_Repair093_41 c2_node c2_sign c3_node) ((shared_expr_Repair093_38 c2_node c2_sign c3_node) ∨ (shared_expr_Repair093_39 c2_node c3_node)) ((shared_expr_Repair093_42 c2_node c3_node) ∨ (shared_expr_Repair093_38 c2_node c2_sign c3_node)))
  have n0 : ((shared_expr_Repair093_41 c2_node c2_sign c3_node) ↔ ((shared_expr_Repair093_38 c2_node c2_sign c3_node) ∨ (shared_expr_Repair093_39 c2_node c3_node))) := by
    exact Iff.mp (normalization_7025 c2_node c2_sign c3_node) (replay_6155 c2_node c2_sign c3_node)
  have n1 : (((shared_expr_Repair093_38 c2_node c2_sign c3_node) ∨ (shared_expr_Repair093_39 c2_node c3_node)) ↔ ((shared_expr_Repair093_42 c2_node c3_node) ∨ (shared_expr_Repair093_38 c2_node c2_sign c3_node))) := by
    exact Iff.mp (normalization_7027 c2_node c2_sign c3_node) (replay_6156 c2_node c2_sign c3_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7028 c2_node c2_sign c3_node) hn

theorem normalized_2051 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7029 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_7030 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_7031 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := (and_congr (normalization_7029 c2_depth c3_depth) (normalization_7030 c2_depth c3_depth))

abbrev shared_expr_Repair093_43 (c2_depth c3_depth : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
theorem normalization_7032 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Repair093_43 c2_depth c3_depth) := (iff_congr (normalization_6882 c2_depth c3_depth) (normalization_7031 c2_depth c3_depth))

-- Checked replay of rewrite.
theorem replay_6158 (c2_depth c3_depth : Int) : (((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2051 (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_7032 c2_depth c3_depth) hn

end H4Formal.Generated.Repair
