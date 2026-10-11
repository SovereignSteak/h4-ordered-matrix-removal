import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification079

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Classification080_0 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((formula_2159 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (formula_2161 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ ((c3_kind = (2 : Int)) ∧ (c3_mode = (0 : Int)) ∧ (c3_level = (0 : Int)) ∧ (c3_group = (0 : Int)) ∧ (c3_depth = (0 : Int)) ∧ (c3_node = (0 : Int)) ∧ (c3_sign = (0 : Int))))
abbrev formula_2163 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_0 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

abbrev shared_expr_Classification080_1 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((formula_2160 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (formula_2162 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ ((c3_kind = (2 : Int)) ∧ (c3_mode = (0 : Int)) ∧ (c3_level = (0 : Int)) ∧ (c3_group = (0 : Int)) ∧ (c3_depth = (0 : Int)) ∧ (c3_node = (0 : Int)) ∧ (c3_sign = (0 : Int))))
abbrev formula_2164 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_1 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

theorem normalized_1847 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ p1) ∧ (p2 ↔ p3)) → ((p0 ∨ p2 ∨ p4) ↔ (p1 ∨ p3 ∨ p4))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification080_2 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ∧ (((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (((c3_level) ≤ (0 : Int)) ∧ (¬ ((c3_level) ≤ (-1 : Int)))) ∧ (((c3_group) ≤ (0 : Int)) ∧ (¬ ((c3_group) ≤ (-1 : Int)))) ∧ (((c3_depth) ≤ (0 : Int)) ∧ (¬ ((c3_depth) ≤ (-1 : Int)))) ∧ (((c3_node) ≤ (0 : Int)) ∧ (¬ ((c3_node) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))))
theorem normalization_7103 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : ((c3_kind = (2 : Int)) ∧ (c3_mode = (0 : Int)) ∧ (c3_level = (0 : Int)) ∧ (c3_group = (0 : Int)) ∧ (c3_depth = (0 : Int)) ∧ (c3_node = (0 : Int)) ∧ (c3_sign = (0 : Int))) ↔ (shared_expr_Classification080_2 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (and_congr (normalization_6545 c3_kind) (and_congr (normalization_6578 c3_mode) (and_congr (normalization_7089 c3_level) (and_congr (normalization_7090 c3_group) (and_congr (normalization_7082 c3_depth) (and_congr (normalization_7083 c3_node) (normalization_6548 c3_sign)))))))

abbrev shared_expr_Classification080_3 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (¬ ((c3_mode) ≤ (-1 : Int))) ∧ ((c3_mode) ≤ (5 : Int)) ∧ (¬ ((c3_level) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ ((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∨ (((c3_group) ≤ (2 : Int)) ∧ (¬ ((c3_group) ≤ (1 : Int))))) ∧ (((c3_depth) ≤ (0 : Int)) ∧ (¬ ((c3_depth) ≤ (-1 : Int)))) ∧ (((c3_node) ≤ (0 : Int)) ∧ (¬ ((c3_node) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))))
abbrev shared_expr_Classification080_4 (c3_depth c3_sign h : Int) : Prop := ((¬ (((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification080_5 (c3_depth c3_sign h : Int) : Prop := (((((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∨ (shared_expr_Classification080_4 c3_depth c3_sign h))
abbrev shared_expr_Classification080_6 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (((c3_level) ≤ (0 : Int)) ∧ (¬ ((c3_level) ≤ (-1 : Int)))) ∧ (((c3_group) ≤ (0 : Int)) ∧ (¬ ((c3_group) ≤ (-1 : Int)))) ∧ (¬ ((c3_depth) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c3_node) ≤ (-1 : Int))) ∧ ((((c3_depth) ≤ (0 : Int)) ∧ (¬ ((c3_depth) ≤ (-1 : Int)))) → (((c3_node) ≤ (0 : Int)) ∧ (¬ ((c3_node) ≤ (-1 : Int))))) ∧ (shared_expr_Classification080_5 c3_depth c3_sign h))
abbrev shared_expr_Classification080_7 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((shared_expr_Classification080_3 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (shared_expr_Classification080_6 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (shared_expr_Classification080_2 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
theorem normalization_7104 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_7 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (or_congr (normalization_7084 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (or_congr (normalization_7098 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7103 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)))

abbrev shared_expr_Classification080_8 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (¬ ((c3_mode) ≤ (-1 : Int))) ∧ (¬ (¬ ((c3_mode) ≤ (5 : Int)))) ∧ (¬ ((c3_level) ≤ (0 : Int))) ∧ ((c3_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ ((((c3_group) ≤ (1 : Int)) ∧ (¬ ((c3_group) ≤ (0 : Int)))) ∨ (((c3_group) ≤ (2 : Int)) ∧ (¬ ((c3_group) ≤ (1 : Int))))) ∧ (((c3_depth) ≤ (0 : Int)) ∧ (¬ ((c3_depth) ≤ (-1 : Int)))) ∧ (((c3_node) ≤ (0 : Int)) ∧ (¬ ((c3_node) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))))
abbrev shared_expr_Classification080_9 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_mode) ≤ (0 : Int)) ∧ (¬ ((c3_mode) ≤ (-1 : Int)))) ∧ (((c3_level) ≤ (0 : Int)) ∧ (¬ ((c3_level) ≤ (-1 : Int)))) ∧ (((c3_group) ≤ (0 : Int)) ∧ (¬ ((c3_group) ≤ (-1 : Int)))) ∧ (¬ ((c3_depth) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c3_node) ≤ (-1 : Int))) ∧ ((¬ (((c3_depth) ≤ (0 : Int)) ∧ (¬ ((c3_depth) ≤ (-1 : Int))))) ∨ (((c3_node) ≤ (0 : Int)) ∧ (¬ ((c3_node) ≤ (-1 : Int))))) ∧ (shared_expr_Classification080_5 c3_depth c3_sign h))
abbrev shared_expr_Classification080_10 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((shared_expr_Classification080_8 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (shared_expr_Classification080_9 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (shared_expr_Classification080_2 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
theorem normalization_7105 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2164 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_10 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (or_congr (normalization_7087 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (or_congr (normalization_7101 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7103 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)))

theorem normalization_7106 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2164 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ↔ ((shared_expr_Classification080_7 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_10 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := (iff_congr (normalization_7104 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7105 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))

-- Checked replay of monotonicity.
theorem replay_5032 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2164 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
  classical
  have ht := (normalized_1847 (shared_expr_Classification080_3 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (shared_expr_Classification080_8 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (shared_expr_Classification080_6 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (shared_expr_Classification080_9 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (shared_expr_Classification080_2 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
  have n0 : ((shared_expr_Classification080_3 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_8 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
    exact Iff.mp (normalization_7088 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (replay_5030 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)
  have n1 : ((shared_expr_Classification080_6 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_9 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
    exact Iff.mp (normalization_7102 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (replay_5031 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7106 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) hn

abbrev shared_expr_Classification080_11 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (((c3_kind = (2 : Int)) ∧ (c3_mode = (0 : Int)) ∧ (c3_level = (0 : Int)) ∧ (c3_group = (0 : Int)) ∧ (c3_depth = (0 : Int)) ∧ (c3_node = (0 : Int)) ∧ (c3_sign = (0 : Int))) ∨ (formula_2160 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (formula_2162 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))
abbrev formula_2165 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_11 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

theorem normalized_1848 (p0 p1 p2 : Prop) : ((p0 ∨ p1 ∨ p2) ↔ (p2 ∨ p0 ∨ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification080_12 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((shared_expr_Classification080_2 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ∨ (shared_expr_Classification080_8 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (shared_expr_Classification080_9 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))
theorem normalization_7107 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (or_congr (normalization_7103 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (or_congr (normalization_7087 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7101 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)))

theorem normalization_7108 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2164 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ↔ ((shared_expr_Classification080_10 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := (iff_congr (normalization_7105 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7107 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))

-- Checked replay of rewrite.
theorem replay_5033 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2164 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
  classical
  have ht := (normalized_1848 (shared_expr_Classification080_8 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (shared_expr_Classification080_9 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (shared_expr_Classification080_2 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_7108 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) hn

theorem normalized_1849 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7109 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ↔ ((shared_expr_Classification080_7 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := (iff_congr (normalization_7104 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7107 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))

-- Checked replay of trans.
theorem replay_5034 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
  classical
  have ht := (normalized_1849 (shared_expr_Classification080_7 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (shared_expr_Classification080_10 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))
  have n0 : ((shared_expr_Classification080_7 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_10 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
    exact Iff.mp (normalization_7106 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (replay_5032 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)
  have n1 : ((shared_expr_Classification080_10 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
    exact Iff.mp (normalization_7108 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (replay_5033 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_7109 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) hn

-- Checked replay of mp.
theorem replay_5035 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) : (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := by
  exact Iff.mp (replay_5034 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) i284

theorem normalized_1850 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7110 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ↔ ((shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := (iff_congr (normalization_7107 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7107 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))

-- Checked replay of rewrite.
theorem replay_5036 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
  classical
  have ht := (normalized_1850 (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))
  have hn := ht
  exact Iff.mpr (normalization_7110 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) hn

-- Checked replay of mp.
theorem replay_5037 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) : (formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := by
  exact Iff.mp (replay_5036 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (replay_5035 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284)

abbrev shared_expr_Classification080_13 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((c3_kind = (0 : Int)) ∧ (c3_mode ≥ (0 : Int)) ∧ (¬ (c3_mode ≥ (6 : Int))) ∧ (c3_level ≥ (1 : Int)) ∧ ((h + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ∧ ((c3_group = (1 : Int)) ∨ (c3_group = (2 : Int))) ∧ (c3_depth = (0 : Int)) ∧ (c3_node = (0 : Int)) ∧ (c3_sign = (0 : Int)))
abbrev formula_2166 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_13 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

abbrev shared_expr_Classification080_14 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((c3_kind = (1 : Int)) ∧ (c3_mode = (0 : Int)) ∧ (c3_level = (0 : Int)) ∧ (c3_group = (0 : Int)) ∧ (c3_depth ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ∧ (c3_node ≥ (0 : Int)) ∧ ((¬ (c3_depth = (0 : Int))) ∨ (c3_node = (0 : Int))) ∧ (((c3_depth = h) ∧ (c3_sign = (2 : Int))) ∨ ((¬ (c3_depth = h)) ∧ ((c3_sign = (0 : Int)) ∨ (c3_sign = (1 : Int))))))
abbrev formula_2167 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_14 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

abbrev shared_expr_Classification080_15 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (((c3_kind = (2 : Int)) ∧ (c3_mode = (0 : Int)) ∧ (c3_level = (0 : Int)) ∧ (c3_group = (0 : Int)) ∧ (c3_depth = (0 : Int)) ∧ (c3_node = (0 : Int)) ∧ (c3_sign = (0 : Int))) ∨ (formula_2166 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (formula_2167 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))
abbrev formula_2168 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_15 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

theorem normalized_1851 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7111 (c3_mode : Int) : (c3_mode ≥ (6 : Int)) ↔ (¬ ((c3_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_7112 (c3_mode : Int) : (¬ (c3_mode ≥ (6 : Int))) ↔ (¬ (¬ ((c3_mode) ≤ (5 : Int)))) := (not_congr (normalization_7111 c3_mode))

theorem normalization_7113 (c3_level h : Int) : ((h + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * h)) ≤ (0 : Int)) := by
  omega

theorem normalization_7114 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2166 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_8 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (and_congr (normalization_6540 c3_kind) (and_congr (normalization_6990 c3_mode) (and_congr (normalization_7112 c3_mode) (and_congr (normalization_7078 c3_level) (and_congr (normalization_7113 c3_level h) (and_congr (normalization_7081 c3_group) (and_congr (normalization_7082 c3_depth) (and_congr (normalization_7083 c3_node) (normalization_6548 c3_sign)))))))))

theorem normalization_7115 (c3_depth h : Int) : ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) := by
  omega

theorem normalization_7116 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2167 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_9 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (and_congr (normalization_6546 c3_kind) (and_congr (normalization_6578 c3_mode) (and_congr (normalization_7089 c3_level) (and_congr (normalization_7090 c3_group) (and_congr (normalization_7091 c3_depth) (and_congr (normalization_7115 c3_depth h) (and_congr (normalization_7093 c3_node) (and_congr (normalization_7100 c3_depth c3_node) (normalization_7097 c3_depth c3_sign h)))))))))

theorem normalization_7117 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2168 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (or_congr (normalization_7103 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (or_congr (normalization_7114 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7116 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)))

theorem normalization_7118 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2168 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ↔ ((shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := (iff_congr (normalization_7107 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7117 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))

-- Checked replay of rewrite.
theorem replay_5038 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2165 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2168 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
  classical
  have ht := (normalized_1851 (shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))
  have hn := ht
  exact Iff.mpr (normalization_7118 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) hn

-- Checked replay of mp.
theorem replay_5039 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) : (formula_2168 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := by
  exact Iff.mp (replay_5038 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (replay_5037 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284)

abbrev shared_expr_Classification080_16 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))) ∨ (¬ (c3_mode ≤ (0 : Int))) ∨ (¬ (c3_mode ≥ (0 : Int))) ∨ (¬ (c3_level ≤ (0 : Int))) ∨ (¬ (c3_level ≥ (0 : Int))) ∨ (¬ (c3_group ≤ (0 : Int))) ∨ (¬ (c3_group ≥ (0 : Int))) ∨ (¬ (c3_depth ≤ (0 : Int))) ∨ (¬ (c3_depth ≥ (0 : Int))) ∨ (¬ (c3_node ≤ (0 : Int))) ∨ (¬ (c3_node ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))
abbrev formula_2169 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_16 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Classification080_17 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((c3_mode ≥ (6 : Int)) ∨ (¬ (c3_mode ≥ (0 : Int))) ∨ (¬ (c3_depth ≤ (0 : Int))) ∨ (¬ (c3_depth ≥ (0 : Int))) ∨ (¬ (c3_node ≤ (0 : Int))) ∨ (¬ (c3_node ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))) ∨ (¬ (c3_level ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_group ≤ (2 : Int))) ∨ (¬ (c3_group ≥ (2 : Int))))))))
abbrev formula_2170 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_17 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

abbrev shared_expr_Classification080_18 (c3_depth c3_sign h : Int) : Prop := (((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ∧ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))))
abbrev shared_expr_Classification080_19 (c3_depth c3_sign h : Int) : Prop := ((shared_expr_Classification080_18 c3_depth c3_sign h) ∨ ((¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))))
abbrev formula_2171 (c3_depth c3_sign h : Int) : Prop := (shared_expr_Classification080_19 c3_depth c3_sign h)

abbrev shared_expr_Classification080_20 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((¬ (c3_mode ≤ (0 : Int))) ∨ (¬ (c3_mode ≥ (0 : Int))) ∨ (¬ (c3_level ≤ (0 : Int))) ∨ (¬ (c3_level ≥ (0 : Int))) ∨ (¬ (c3_group ≤ (0 : Int))) ∨ (¬ (c3_group ≥ (0 : Int))) ∨ (¬ (c3_depth ≥ (0 : Int))) ∨ (¬ (c3_node ≥ (0 : Int))) ∨ (¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((¬ (c3_depth ≤ (0 : Int))) ∨ (¬ (c3_depth ≥ (0 : Int))) ∨ (¬ ((¬ (c3_node ≤ (0 : Int))) ∨ (¬ (c3_node ≥ (0 : Int))))))) ∨ (¬ (formula_2171 c3_depth c3_sign h)))
abbrev formula_2172 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_20 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

abbrev shared_expr_Classification080_21 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((¬ (formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) ∨ (¬ (formula_2170 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ∨ (¬ (formula_2172 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)))
abbrev formula_2173 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := (shared_expr_Classification080_21 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)

theorem normalized_1852 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p14 ∧ (¬ p15)) ∧ (¬ p3) ∧ (¬ (¬ p16)) ∧ (¬ p4) ∧ p17 ∧ ((p18 ∧ (¬ p6)) ∨ (p19 ∧ (¬ p18))) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p1 ∧ (¬ p14)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (¬ p9) ∧ p20 ∧ (¬ p11) ∧ ((¬ (p8 ∧ (¬ p9))) ∨ (p10 ∧ (¬ p11))) ∧ (((p20 ∧ (¬ p21)) ∧ (p22 ∧ (¬ p23))) ∨ ((¬ (p20 ∧ (¬ p21))) ∧ ((p12 ∧ (¬ p13)) ∨ (p23 ∧ (¬ p12))))))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ p10) ∨ (¬ (¬ p11)) ∨ (¬ p12) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p16) ∨ (¬ (¬ p3)) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ p10) ∨ (¬ (¬ p11)) ∨ (¬ p12) ∨ (¬ (¬ p13)) ∨ (¬ p14) ∨ (¬ (¬ p15)) ∨ (¬ (¬ p4)) ∨ (¬ p17) ∨ (¬ ((¬ ((¬ p18) ∨ (¬ (¬ p6)))) ∨ (¬ ((¬ p19) ∨ (¬ (¬ p18)))))))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ (¬ p9)) ∨ (¬ (¬ p11)) ∨ (¬ p1) ∨ (¬ (¬ p14)) ∨ (¬ p20) ∨ (¬ ((¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ ((¬ p10) ∨ (¬ (¬ p11)))))) ∨ (¬ ((((¬ p20) ∨ (¬ (¬ p21))) ∧ ((¬ ((¬ p12) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p23) ∨ (¬ (¬ p12)))))) ∨ ((¬ ((¬ p20) ∨ (¬ (¬ p21)))) ∧ (¬ ((¬ p22) ∨ (¬ (¬ p23))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7119 (c3_level : Int) : (c3_level ≤ (0 : Int)) ↔ ((c3_level) ≤ (0 : Int)) := by
  omega

theorem normalization_7120 (c3_level : Int) : (¬ (c3_level ≤ (0 : Int))) ↔ (¬ ((c3_level) ≤ (0 : Int))) := (not_congr (normalization_7119 c3_level))

theorem normalization_7121 (c3_level : Int) : (c3_level ≥ (0 : Int)) ↔ (¬ ((c3_level) ≤ (-1 : Int))) := by
  omega

theorem normalization_7122 (c3_level : Int) : (¬ (c3_level ≥ (0 : Int))) ↔ (¬ (¬ ((c3_level) ≤ (-1 : Int)))) := (not_congr (normalization_7121 c3_level))

theorem normalization_7123 (c3_group : Int) : (c3_group ≤ (0 : Int)) ↔ ((c3_group) ≤ (0 : Int)) := by
  omega

theorem normalization_7124 (c3_group : Int) : (¬ (c3_group ≤ (0 : Int))) ↔ (¬ ((c3_group) ≤ (0 : Int))) := (not_congr (normalization_7123 c3_group))

theorem normalization_7125 (c3_group : Int) : (c3_group ≥ (0 : Int)) ↔ (¬ ((c3_group) ≤ (-1 : Int))) := by
  omega

theorem normalization_7126 (c3_group : Int) : (¬ (c3_group ≥ (0 : Int))) ↔ (¬ (¬ ((c3_group) ≤ (-1 : Int)))) := (not_congr (normalization_7125 c3_group))

theorem normalization_7127 (c3_depth : Int) : (c3_depth ≤ (0 : Int)) ↔ ((c3_depth) ≤ (0 : Int)) := by
  omega

theorem normalization_7128 (c3_depth : Int) : (¬ (c3_depth ≤ (0 : Int))) ↔ (¬ ((c3_depth) ≤ (0 : Int))) := (not_congr (normalization_7127 c3_depth))

theorem normalization_7129 (c3_depth : Int) : (¬ (c3_depth ≥ (0 : Int))) ↔ (¬ (¬ ((c3_depth) ≤ (-1 : Int)))) := (not_congr (normalization_7091 c3_depth))

theorem normalization_7130 (c3_node : Int) : (c3_node ≤ (0 : Int)) ↔ ((c3_node) ≤ (0 : Int)) := by
  omega

theorem normalization_7131 (c3_node : Int) : (¬ (c3_node ≤ (0 : Int))) ↔ (¬ ((c3_node) ≤ (0 : Int))) := (not_congr (normalization_7130 c3_node))

theorem normalization_7132 (c3_node : Int) : (¬ (c3_node ≥ (0 : Int))) ↔ (¬ (¬ ((c3_node) ≤ (-1 : Int)))) := (not_congr (normalization_7093 c3_node))

abbrev shared_expr_Classification080_22 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))) ∨ (¬ ((c3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_mode) ≤ (-1 : Int)))) ∨ (¬ ((c3_level) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_level) ≤ (-1 : Int)))) ∨ (¬ ((c3_group) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth) ≤ (-1 : Int)))) ∨ (¬ ((c3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_node) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))
theorem normalization_7133 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification080_22 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (or_congr (normalization_6835 c3_kind) (or_congr (normalization_6837 c3_kind) (or_congr (normalization_6989 c3_mode) (or_congr (normalization_6991 c3_mode) (or_congr (normalization_7120 c3_level) (or_congr (normalization_7122 c3_level) (or_congr (normalization_7124 c3_group) (or_congr (normalization_7126 c3_group) (or_congr (normalization_7128 c3_depth) (or_congr (normalization_7129 c3_depth) (or_congr (normalization_7131 c3_node) (or_congr (normalization_7132 c3_node) (or_congr (normalization_6815 c3_sign) (normalization_6817 c3_sign))))))))))))))

theorem normalization_7134 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (¬ (formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) ↔ (¬ (shared_expr_Classification080_22 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) := (not_congr (normalization_7133 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

theorem normalization_7135 (c3_level : Int) : (¬ (c3_level ≥ (1 : Int))) ↔ (¬ (¬ ((c3_level) ≤ (0 : Int)))) := (not_congr (normalization_7078 c3_level))

theorem normalization_7136 (c3_level h : Int) : (¬ ((h + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * h)) ≤ (0 : Int))) := (not_congr (normalization_7113 c3_level h))

theorem normalization_7137 (c3_group : Int) : (¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ↔ (¬ ((¬ ((c3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (0 : Int)))))) := (not_congr (normalization_6996 c3_group))

theorem normalization_7138 (c3_group : Int) : (c3_group ≤ (2 : Int)) ↔ ((c3_group) ≤ (2 : Int)) := by
  omega

theorem normalization_7139 (c3_group : Int) : (¬ (c3_group ≤ (2 : Int))) ↔ (¬ ((c3_group) ≤ (2 : Int))) := (not_congr (normalization_7138 c3_group))

theorem normalization_7140 (c3_group : Int) : (c3_group ≥ (2 : Int)) ↔ (¬ ((c3_group) ≤ (1 : Int))) := by
  omega

theorem normalization_7141 (c3_group : Int) : (¬ (c3_group ≥ (2 : Int))) ↔ (¬ (¬ ((c3_group) ≤ (1 : Int)))) := (not_congr (normalization_7140 c3_group))

theorem normalization_7142 (c3_group : Int) : ((¬ (c3_group ≤ (2 : Int))) ∨ (¬ (c3_group ≥ (2 : Int)))) ↔ ((¬ ((c3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (1 : Int))))) := (or_congr (normalization_7139 c3_group) (normalization_7141 c3_group))

theorem normalization_7143 (c3_group : Int) : (¬ ((¬ (c3_group ≤ (2 : Int))) ∨ (¬ (c3_group ≥ (2 : Int))))) ↔ (¬ ((¬ ((c3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (1 : Int)))))) := (not_congr (normalization_7142 c3_group))

theorem normalization_7144 (c3_group : Int) : ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_group ≤ (2 : Int))) ∨ (¬ (c3_group ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (1 : Int))))))) := (or_congr (normalization_7137 c3_group) (normalization_7143 c3_group))

theorem normalization_7145 (c3_group : Int) : (¬ ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_group ≤ (2 : Int))) ∨ (¬ (c3_group ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (1 : Int)))))))) := (not_congr (normalization_7144 c3_group))

abbrev shared_expr_Classification080_23 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((¬ ((c3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c3_mode) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth) ≤ (-1 : Int)))) ∨ (¬ ((c3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_node) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_level) ≤ (0 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ ((¬ ((¬ ((c3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (1 : Int)))))))))
theorem normalization_7146 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2170 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_23 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (or_congr (normalization_7111 c3_mode) (or_congr (normalization_6991 c3_mode) (or_congr (normalization_7128 c3_depth) (or_congr (normalization_7129 c3_depth) (or_congr (normalization_7131 c3_node) (or_congr (normalization_7132 c3_node) (or_congr (normalization_6815 c3_sign) (or_congr (normalization_6817 c3_sign) (or_congr (normalization_6743 c3_kind) (or_congr (normalization_6744 c3_kind) (or_congr (normalization_7135 c3_level) (or_congr (normalization_7136 c3_level h) (normalization_7145 c3_group)))))))))))))

theorem normalization_7147 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (¬ (formula_2170 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ↔ (¬ (shared_expr_Classification080_23 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := (not_congr (normalization_7146 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))

theorem normalization_7148 (c3_depth h : Int) : (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int))) := (not_congr (normalization_7115 c3_depth h))

theorem normalization_7149 (c3_node : Int) : ((¬ (c3_node ≤ (0 : Int))) ∨ (¬ (c3_node ≥ (0 : Int)))) ↔ ((¬ ((c3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_node) ≤ (-1 : Int))))) := (or_congr (normalization_7131 c3_node) (normalization_7132 c3_node))

theorem normalization_7150 (c3_node : Int) : (¬ ((¬ (c3_node ≤ (0 : Int))) ∨ (¬ (c3_node ≥ (0 : Int))))) ↔ (¬ ((¬ ((c3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_node) ≤ (-1 : Int)))))) := (not_congr (normalization_7149 c3_node))

theorem normalization_7151 (c3_depth c3_node : Int) : ((¬ (c3_depth ≤ (0 : Int))) ∨ (¬ (c3_depth ≥ (0 : Int))) ∨ (¬ ((¬ (c3_node ≤ (0 : Int))) ∨ (¬ (c3_node ≥ (0 : Int)))))) ↔ ((¬ ((c3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((c3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_node) ≤ (-1 : Int))))))) := (or_congr (normalization_7128 c3_depth) (or_congr (normalization_7129 c3_depth) (normalization_7150 c3_node)))

theorem normalization_7152 (c3_depth c3_node : Int) : (¬ ((¬ (c3_depth ≤ (0 : Int))) ∨ (¬ (c3_depth ≥ (0 : Int))) ∨ (¬ ((¬ (c3_node ≤ (0 : Int))) ∨ (¬ (c3_node ≥ (0 : Int))))))) ↔ (¬ ((¬ ((c3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((c3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_node) ≤ (-1 : Int)))))))) := (not_congr (normalization_7151 c3_depth c3_node))

theorem normalization_7153 (c3_depth h : Int) : ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7154 (c3_depth h : Int) : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (not_congr (normalization_7153 c3_depth h))

theorem normalization_7155 (c3_depth h : Int) : ((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ↔ ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) := (or_congr (normalization_7148 c3_depth h) (normalization_7154 c3_depth h))

theorem normalization_7156 (c3_sign : Int) : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (or_congr (normalization_6819 c3_sign) (normalization_6849 c3_sign))

abbrev shared_expr_Classification080_24 (c3_depth c3_sign h : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))))
abbrev shared_expr_Classification080_25 (c3_depth c3_sign h : Int) : Prop := ((shared_expr_Classification080_24 c3_depth c3_sign h) ∨ ((¬ ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
theorem normalization_7157 (c3_depth c3_sign h : Int) : (formula_2171 c3_depth c3_sign h) ↔ (shared_expr_Classification080_25 c3_depth c3_sign h) := (or_congr (and_congr (normalization_7155 c3_depth h) (normalization_7156 c3_sign)) (and_congr (not_congr (normalization_7155 c3_depth h)) (normalization_6825 c3_sign)))

theorem normalization_7158 (c3_depth c3_sign h : Int) : (¬ (formula_2171 c3_depth c3_sign h)) ↔ (¬ (shared_expr_Classification080_25 c3_depth c3_sign h)) := (not_congr (normalization_7157 c3_depth c3_sign h))

abbrev shared_expr_Classification080_26 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((¬ ((c3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_mode) ≤ (-1 : Int)))) ∨ (¬ ((c3_level) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_level) ≤ (-1 : Int)))) ∨ (¬ ((c3_group) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_group) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_depth) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node) ≤ (-1 : Int)))) ∨ (¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ ((¬ ((c3_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((c3_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_node) ≤ (-1 : Int)))))))) ∨ (¬ (shared_expr_Classification080_25 c3_depth c3_sign h)))
theorem normalization_7159 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2172 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_26 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (or_congr (normalization_6989 c3_mode) (or_congr (normalization_6991 c3_mode) (or_congr (normalization_7120 c3_level) (or_congr (normalization_7122 c3_level) (or_congr (normalization_7124 c3_group) (or_congr (normalization_7126 c3_group) (or_congr (normalization_7129 c3_depth) (or_congr (normalization_7132 c3_node) (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_7148 c3_depth h) (or_congr (normalization_7152 c3_depth c3_node) (normalization_7158 c3_depth c3_sign h)))))))))))))

theorem normalization_7160 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (¬ (formula_2172 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ↔ (¬ (shared_expr_Classification080_26 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := (not_congr (normalization_7159 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))

abbrev shared_expr_Classification080_27 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : Prop := ((¬ (shared_expr_Classification080_22 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) ∨ (¬ (shared_expr_Classification080_23 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ∨ (¬ (shared_expr_Classification080_26 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)))
theorem normalization_7161 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : (formula_2173 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_27 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := (or_congr (normalization_7134 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (or_congr (normalization_7147 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7160 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)))

theorem normalization_7162 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2168 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2173 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) ↔ ((shared_expr_Classification080_12 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (shared_expr_Classification080_27 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := (iff_congr (normalization_7117 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (normalization_7161 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h))

-- Checked replay of rewrite.
theorem replay_5040 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2168 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ↔ (formula_2173 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
  classical
  have ht := (normalized_1852 ((c3_kind) ≤ (2 : Int)) ((c3_kind) ≤ (1 : Int)) ((c3_mode) ≤ (0 : Int)) ((c3_mode) ≤ (-1 : Int)) ((c3_level) ≤ (0 : Int)) ((c3_level) ≤ (-1 : Int)) ((c3_group) ≤ (0 : Int)) ((c3_group) ≤ (-1 : Int)) ((c3_depth) ≤ (0 : Int)) ((c3_depth) ≤ (-1 : Int)) ((c3_node) ≤ (0 : Int)) ((c3_node) ≤ (-1 : Int)) ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (-1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)) ((c3_mode) ≤ (5 : Int)) ((c3_level + ((-1 : Int) * h)) ≤ (0 : Int)) ((c3_group) ≤ (1 : Int)) ((c3_group) ≤ (2 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c3_sign) ≤ (2 : Int)) ((c3_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7162 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) hn

-- Checked replay of mp.
theorem replay_5041 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) : (formula_2173 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := by
  exact Iff.mp (replay_5040 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (replay_5039 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284)

theorem propositional_1853 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p7))))) ∨ (¬ ((((¬ p10) ∨ (¬ p13)) ∧ ((¬ ((¬ p14) ∨ (¬ p15))) ∨ (¬ ((¬ p16) ∨ (¬ p17))))) ∨ ((¬ ((¬ p10) ∨ (¬ p13))) ∧ (¬ ((¬ p18) ∨ (¬ p19))))))) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5042 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2172 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (c3_depth ≥ (0 : Int))) := by
  exact (propositional_1853 (c3_mode ≤ (0 : Int)) (c3_mode ≥ (0 : Int)) (c3_level ≤ (0 : Int)) (c3_level ≥ (0 : Int)) (c3_group ≤ (0 : Int)) (c3_group ≥ (0 : Int)) (c3_depth ≥ (0 : Int)) (c3_node ≥ (0 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) (c3_depth ≤ (0 : Int)) (c3_node ≤ (0 : Int)) ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5043 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i285 : (¬ (c3_depth ≥ (0 : Int)))) : (formula_2172 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := by
  exact (Or.elim (replay_5042 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i285 t0))))

theorem propositional_1854 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5044 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2170 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (c3_depth ≥ (0 : Int))) := by
  exact (propositional_1854 (c3_mode ≥ (6 : Int)) (c3_mode ≥ (0 : Int)) (c3_depth ≤ (0 : Int)) (c3_depth ≥ (0 : Int)) (c3_node ≤ (0 : Int)) (c3_node ≥ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (c3_kind ≤ (0 : Int)) (c3_kind ≥ (0 : Int)) (c3_level ≥ (1 : Int)) ((h + ((-1 : Int) * c3_level)) ≥ (0 : Int)) (c3_group ≤ (1 : Int)) (c3_group ≥ (1 : Int)) (c3_group ≤ (2 : Int)) (c3_group ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5045 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i285 : (¬ (c3_depth ≥ (0 : Int)))) : (formula_2170 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := by
  exact (Or.elim (replay_5044 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i285 t0))))

-- Checked replay of unit-resolution.
theorem replay_5046 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i285 : (¬ (c3_depth ≥ (0 : Int)))) (i286 : (formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : False := by
  exact (Or.elim (replay_5041 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284) (fun l0 => (False.elim (l0 i286))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5045 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i285)))) (fun t1 => (False.elim (t1 (replay_5043 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i285)))))))

-- Checked replay of lemma.
theorem replay_5047 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) : ((c3_depth ≥ (0 : Int)) ∨ (¬ (formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5046 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284 (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr q))))

theorem propositional_1855 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p9) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5048 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : ((formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ∨ (c3_depth ≥ (0 : Int))) := by
  exact (propositional_1855 (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)) (c3_mode ≤ (0 : Int)) (c3_mode ≥ (0 : Int)) (c3_level ≤ (0 : Int)) (c3_level ≥ (0 : Int)) (c3_group ≤ (0 : Int)) (c3_group ≥ (0 : Int)) (c3_depth ≤ (0 : Int)) (c3_depth ≥ (0 : Int)) (c3_node ≤ (0 : Int)) (c3_node ≥ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5049 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i285 : (¬ (c3_depth ≥ (0 : Int)))) : (formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact (Or.elim (replay_5048 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i285 t0))))

-- Checked replay of unit-resolution.
theorem replay_5050 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i285 : (¬ (c3_depth ≥ (0 : Int)))) : False := by
  exact (Or.elim (replay_5047 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284) (fun l0 => (False.elim (i285 l0))) (fun t0 => (False.elim (t0 (replay_5049 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i285)))))

-- Checked replay of lemma.
theorem replay_5051 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) : (c3_depth ≥ (0 : Int)) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5050 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284 (fun q => nc q))

-- Checked replay of unit-resolution.
theorem replay_5052 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) : ((¬ (r1_level ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  exact (Or.elim (replay_5029 c3_depth r1_level) (fun l0 => (False.elim (l0 (replay_5051 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284)))) (fun t0 => (Or.elim t0 (fun l1 => (Or.inl l1)) (fun t1 => (Or.inr t1)))))

-- Checked replay of unit-resolution.
theorem replay_5053 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) := by
  exact (Or.elim (replay_5052 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level i284) (fun l0 => (False.elim (l0 (replay_4129 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i11)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5054 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_2023 c3_depth c3_kind c3_sign r1_level) := by
  exact (Or.elim (replay_5028 c3_depth c3_kind c3_sign r1_level) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim ((replay_5053 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i284 i11) t0))))

-- Checked replay of unit-resolution.
theorem replay_5055 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (¬ (formula_2030 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := by
  exact (Or.elim (replay_5027 c3_depth c3_kind c3_node c3_sign r1_group r1_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i287))) (fun t1 => (False.elim (t1 (replay_5054 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i284 i11)))))))

-- Checked replay of unit-resolution.
theorem replay_5056 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2030 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_5026 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5055 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i284 i287 i11) t0))))

-- Checked replay of th-lemma.
theorem replay_5057 (r1_mode : Int) : ((r1_mode ≥ (1 : Int)) ∨ (¬ (r1_mode ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_5058 (r1_mode : Int) : ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_5059 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (¬ (r1_mode ≥ (1 : Int))) := by
  exact (Or.elim (replay_5058 r1_mode) (fun l0 => (False.elim (l0 (replay_97 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i10 i11)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5060 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (¬ (r1_mode ≥ (2 : Int))) := by
  exact (Or.elim (replay_5057 r1_mode) (fun l0 => (False.elim ((replay_5059 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i10 i11) l0))) (fun t0 => t0))

theorem propositional_1856 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((¬ p8) ∨ (¬ p9))))) ∨ (¬ p10) ∨ (¬ p11)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p12) ∨ (¬ p13))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5061 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2024 c3_depth c3_kind c3_sign r1_group r1_level))) ∨ (r1_mode ≥ (1 : Int))) := by
  exact (propositional_1856 (r1_mode ≤ (1 : Int)) (r1_mode ≥ (1 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5062 (c3_depth c3_kind c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2024 c3_depth c3_kind c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_5061 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5059 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i10 i11) t0))))

theorem propositional_1857 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5063 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level))) ∨ (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level)) := by
  exact (propositional_1857 (r1_mode ≤ (0 : Int)) (r1_mode ≥ (0 : Int)) (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level))

theorem propositional_1858 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5064 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : ((¬ (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) := by
  exact (propositional_1858 ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) (formula_2021 c3_depth c3_kind c3_sign r1_level) (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)))

theorem propositional_1859 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5065 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : ((formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ∨ (c3_kind ≥ (2 : Int))) := by
  exact (propositional_1859 (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)) (c3_mode ≤ (0 : Int)) (c3_mode ≥ (0 : Int)) (c3_level ≤ (0 : Int)) (c3_level ≥ (0 : Int)) (c3_group ≤ (0 : Int)) (c3_group ≥ (0 : Int)) (c3_depth ≤ (0 : Int)) (c3_depth ≥ (0 : Int)) (c3_node ≤ (0 : Int)) (c3_node ≥ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_5066 (c3_kind : Int) : ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1860 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5067 (c3_depth c3_kind c3_sign r1_level : Int) : ((formula_2021 c3_depth c3_kind c3_sign r1_level) ∨ (c3_kind ≤ (1 : Int))) := by
  exact (propositional_1860 (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5068 (c3_depth c3_kind c3_sign r1_level : Int) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (c3_kind ≤ (1 : Int)) := by
  exact (Or.elim (replay_5067 c3_depth c3_kind c3_sign r1_level) (fun l0 => (False.elim (i288 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5069 (c3_depth c3_kind c3_sign r1_level : Int) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (¬ (c3_kind ≥ (2 : Int))) := by
  exact (Or.elim (replay_5066 c3_kind) (fun l0 => (False.elim (l0 (replay_5068 c3_depth c3_kind c3_sign r1_level i288)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5070 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_level : Int) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (formula_2169 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact (Or.elim (replay_5065 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_5069 c3_depth c3_kind c3_sign r1_level i288) t0))))

theorem propositional_1861 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p8) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5071 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h : Int) : ((formula_2170 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) ∨ (c3_kind ≤ (0 : Int))) := by
  exact (propositional_1861 (c3_mode ≥ (6 : Int)) (c3_mode ≥ (0 : Int)) (c3_depth ≤ (0 : Int)) (c3_depth ≥ (0 : Int)) (c3_node ≤ (0 : Int)) (c3_node ≥ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (c3_kind ≤ (0 : Int)) (c3_kind ≥ (0 : Int)) (c3_level ≥ (1 : Int)) ((h + ((-1 : Int) * c3_level)) ≥ (0 : Int)) (c3_group ≤ (1 : Int)) (c3_group ≥ (1 : Int)) (c3_group ≤ (2 : Int)) (c3_group ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_5072 (c3_kind : Int) : ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1862 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5073 (c3_depth c3_kind c3_sign r1_level : Int) : ((formula_2021 c3_depth c3_kind c3_sign r1_level) ∨ (c3_kind ≥ (1 : Int))) := by
  exact (propositional_1862 (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5074 (c3_depth c3_kind c3_sign r1_level : Int) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (c3_kind ≥ (1 : Int)) := by
  exact (Or.elim (replay_5073 c3_depth c3_kind c3_sign r1_level) (fun l0 => (False.elim (i288 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5075 (c3_depth c3_kind c3_sign r1_level : Int) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (¬ (c3_kind ≤ (0 : Int))) := by
  exact (Or.elim (replay_5072 c3_kind) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_5074 c3_depth c3_kind c3_sign r1_level i288)))))

-- Checked replay of unit-resolution.
theorem replay_5076 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level : Int) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (formula_2170 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) := by
  exact (Or.elim (replay_5071 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_5075 c3_depth c3_kind c3_sign r1_level i288) t0))))

-- Checked replay of unit-resolution.
theorem replay_5077 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (¬ (formula_2172 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) := by
  exact (Or.elim (replay_5041 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h i284) (fun l0 => (False.elim (l0 (replay_5070 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_level i288)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5076 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level i288)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_5078 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (c3_depth ≥ (0 : Int)) := by
  exact (Or.elim (replay_5042 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h) (fun l0 => (False.elim ((replay_5077 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level i284 i288) l0))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_5079 (c3_depth r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1863 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5080 (c3_depth c3_kind c3_sign r1_level : Int) : ((formula_2021 c3_depth c3_kind c3_sign r1_level) ∨ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) := by
  exact (propositional_1863 (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5081 (c3_depth c3_kind c3_sign r1_level : Int) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) := by
  exact (Or.elim (replay_5080 c3_depth c3_kind c3_sign r1_level) (fun l0 => (False.elim (i288 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5082 (c3_depth c3_kind c3_sign r1_level : Int) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_5079 c3_depth r1_level) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_5081 c3_depth c3_kind c3_sign r1_level i288)))))

-- Checked replay of th-lemma.
theorem replay_5083 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i289 : (r1_level ≤ (0 : Int))) (i288 : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level))) : False := by
  classical
  have k0 := (replay_5078 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level i284 i288)
  have k1 := i289
  have k2 := (replay_5082 c3_depth c3_kind c3_sign r1_level i288)
  first | omega | grind (splits := 40)

-- Checked replay of lemma.
theorem replay_5084 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level : Int) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) : ((formula_2021 c3_depth c3_kind c3_sign r1_level) ∨ (¬ (r1_level ≤ (0 : Int)))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5083 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level i284 (Classical.byContradiction (fun q => nc (Or.inr q))) (fun q => nc (Or.inl q)))

-- Checked replay of unit-resolution.
theorem replay_5085 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_2021 c3_depth c3_kind c3_sign r1_level) := by
  exact (Or.elim (replay_5084 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_level i284) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim (t0 (replay_4129 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i11)))))

-- Checked replay of unit-resolution.
theorem replay_5086 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (¬ (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level)) := by
  exact (Or.elim (replay_5064 c3_depth c3_kind c3_sign r1_group r1_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i287))) (fun t1 => (False.elim (t1 (replay_5085 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i284 i11)))))))

-- Checked replay of unit-resolution.
theorem replay_5087 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_5063 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5086 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i284 i287 i11) t0))))

-- Checked replay of unit-resolution.
theorem replay_5088 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i281 : (formula_2033 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : False := by
  exact (Or.elim (replay_5025 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => (False.elim ((replay_5060 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i10 i11) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i281))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_5087 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i284 i287 i11)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_5062 c3_depth c3_kind c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i10 i11)))) (fun t3 => (False.elim (t3 (replay_5056 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i6 i284 i287 i11)))))))))))

abbrev shared_expr_Classification080_28 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ∨ (¬ (formula_2033 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) ∨ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))))
abbrev formula_2174 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Classification080_28 c3_depth c3_kind c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

-- Checked replay of lemma.
theorem replay_5089 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (formula_2174 c3_depth c3_kind c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5088 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i284 i10 (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))) (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

-- Checked replay of unit-resolution.
theorem replay_5090 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i6 : (formula_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i284 : (formula_2163 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h)) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i287 : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) (i11 : (formula_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (¬ (formula_2033 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) := by
  exact (Or.elim (replay_5089 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i6 i284 i10) (fun l0 => (False.elim (l0 i11))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 i287))))))

abbrev shared_expr_Classification080_29 (c2_node c3_node : Int) : Prop := (((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))))
abbrev shared_expr_Classification080_30 (c2_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev formula_2175 (c2_node c3_node c3_sign : Int) : Prop := ((shared_expr_Classification080_29 c2_node c3_node) ∨ (shared_expr_Classification080_30 c2_node c3_node c3_sign))

abbrev shared_expr_Classification080_31 (c2_node c3_node : Int) : Prop := (((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev shared_expr_Classification080_32 (c2_node c2_sign c3_node : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))))
abbrev formula_2176 (c2_node c2_sign c3_node : Int) : Prop := ((shared_expr_Classification080_31 c2_node c3_node) ∨ (shared_expr_Classification080_32 c2_node c2_sign c3_node))

abbrev shared_expr_Classification080_33 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_2175 c2_node c3_node c3_sign)))
abbrev shared_expr_Classification080_34 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((shared_expr_Classification080_33 c2_depth c2_node c3_depth c3_node c3_sign) ∨ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ∧ (formula_2176 c2_node c2_sign c3_node)))
abbrev formula_2177 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_34 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Classification080_35 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification080_36 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ∨ (shared_expr_Classification080_35 c2_node c2_sign c3_node c3_sign))
abbrev formula_2178 (c2_node c2_sign c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_36 c2_node c2_sign c3_node c3_sign)

abbrev shared_expr_Classification080_37 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ∧ (formula_2177 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ∨ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ∧ (formula_2178 c2_node c2_sign c3_node c3_sign)))
abbrev formula_2179 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_37 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Classification080_38 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ∧ (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2179 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))))) ∨ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))))
abbrev formula_2180 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_38 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Classification080_39 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))) ∨ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))
abbrev formula_2181 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_39 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem propositional_1864 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 : Prop) : (((¬ p0) ∨ (¬ ((((¬ p1) ∨ (¬ p2)) ∧ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((((¬ p5) ∨ (¬ p6)) ∧ ((((¬ p7) ∨ (¬ p8)) ∧ ((¬ p9) ∨ (¬ p10) ∨ ((((¬ p11) ∨ (¬ p12)) ∧ (¬ p11)) ∨ ((¬ ((¬ p11) ∨ (¬ p12))) ∧ (¬ ((¬ p13) ∨ (¬ p14))))))) ∨ ((¬ ((¬ p7) ∨ (¬ p8))) ∧ ((((¬ p15) ∨ (¬ p16)) ∧ (¬ p16)) ∨ ((¬ ((¬ p15) ∨ (¬ p16))) ∧ (¬ ((¬ p17) ∨ (¬ p18)))))))) ∨ ((¬ ((¬ p5) ∨ (¬ p6))) ∧ ((((¬ p19) ∨ (¬ p20)) ∧ (¬ p20)) ∨ ((¬ ((¬ p19) ∨ (¬ p20))) ∧ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ p13) ∨ (¬ p14))))))))))) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ (¬ ((¬ p21) ∨ (¬ p22))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5091 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2181 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  exact (propositional_1864 ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) (c2_kind ≤ (2 : Int)) (c2_kind ≥ (2 : Int)) (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)))

abbrev shared_expr_Classification080_40 (c2_group c2_mode c3_group c3_mode : Int) : Prop := ((((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ∧ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2182 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (shared_expr_Classification080_40 c2_group c2_mode c3_group c3_mode)

abbrev shared_expr_Classification080_41 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ∧ (formula_2182 c2_group c2_mode c3_group c3_mode)))
abbrev formula_2183 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (shared_expr_Classification080_41 c2_group c2_level c2_mode c3_group c3_level c3_mode)

abbrev shared_expr_Classification080_42 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2183 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))))
abbrev formula_2184 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))) ∨ (shared_expr_Classification080_42 c2_group c2_level c2_mode c3_group c3_level c3_mode))

abbrev shared_expr_Classification080_43 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∧ (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev shared_expr_Classification080_44 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification080_43 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ∨ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∧ (formula_2184 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)))
abbrev formula_2185 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_44 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Classification080_45 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))) ∨ (¬ (formula_2185 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)))
abbrev formula_2186 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_45 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem propositional_1865 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ p0) ∨ (¬ p1) ∨ (¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ ((¬ p2) ∨ (¬ p3) ∨ (((p4 ↔ p5) ∧ ((((¬ p6) ∨ (¬ p7)) ∧ (¬ p7)) ∨ ((¬ ((¬ p6) ∨ (¬ p7))) ∧ ((((¬ p8) ∨ (¬ p9)) ∧ (¬ p9)) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ (¬ p10)))))) ∨ ((¬ (p4 ↔ p5)) ∧ p4))))))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5092 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2186 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact (propositional_1865 ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2180 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))) (c3_kind ≤ (0 : Int)) (c3_kind ≥ (0 : Int)) (c2_mode ≥ (4 : Int)) (c3_mode ≥ (4 : Int)) ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)) ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))

abbrev shared_expr_Classification080_46 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((¬ (¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))))) ∧ (((c2_level ≠ c3_level) ∧ (c2_level < c3_level)) ∨ ((¬ (c2_level ≠ c3_level)) ∧ (((c2_mode ≠ c3_mode) ∧ (c2_mode < c3_mode)) ∨ ((¬ (c2_mode ≠ c3_mode)) ∧ (c2_group < c3_group))))))
abbrev formula_2187 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))) ∨ (shared_expr_Classification080_46 c2_group c2_level c2_mode c3_group c3_level c3_mode))

abbrev shared_expr_Classification080_47 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((((c3_depth + (1 : Int)) = c2_depth) ∧ (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ ((c2_node / (2 : Int)) < c3_node)))) ∨ ((¬ ((c3_depth + (1 : Int)) = c2_depth)) ∧ True))
abbrev formula_2188 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_47 c2_depth c2_node c3_depth c3_node c3_sign)

abbrev shared_expr_Classification080_48 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((((c2_depth + (1 : Int)) = c3_depth) ∧ (((c2_node = (c3_node / (2 : Int))) ∧ (c2_sign = (0 : Int))) ∨ ((¬ (c2_node = (c3_node / (2 : Int)))) ∧ (c2_node < (c3_node / (2 : Int)))))) ∨ ((¬ ((c2_depth + (1 : Int)) = c3_depth)) ∧ (formula_2188 c2_depth c2_node c3_depth c3_node c3_sign)))
abbrev formula_2189 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_48 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Classification080_49 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((c2_depth = c3_depth) ∧ (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (c2_node < c3_node)))) ∨ ((¬ (c2_depth = c3_depth)) ∧ (formula_2189 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev formula_2190 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_49 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Classification080_50 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((c2_kind = (2 : Int)) ∧ (True ∧ (c3_kind = (1 : Int)))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ (((c3_kind = (2 : Int)) ∧ False) ∨ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2190 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev formula_2191 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_50 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Classification080_51 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((c2_kind = (0 : Int)) ∧ (((c3_kind = (0 : Int)) ∧ (formula_2187 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ (c3_kind = (0 : Int))) ∧ True))) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (((c3_kind = (0 : Int)) ∧ False) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2191 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev formula_2192 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_51 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Classification080_52 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (((c2_level = c3_level) ∧ (((c2_mode = c3_mode) ∧ (¬ (c3_group ≤ c2_group))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ (c3_mode ≤ c2_mode))))) ∨ ((¬ (c2_level = c3_level)) ∧ (¬ (c3_level ≤ c2_level)))))
abbrev formula_2193 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((shared_expr_Classification080_52 c2_group c2_level c2_mode c3_group c3_level c3_mode) ∨ ((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))))

abbrev shared_expr_Classification080_53 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (c2_depth = ((-1 : Int) + c3_depth))) ∧ ((¬ (c3_depth = ((-1 : Int) + c2_depth))) ∨ (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ (¬ (c3_node ≤ (c2_node / (2 : Int))))))))
abbrev shared_expr_Classification080_54 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((c2_depth = ((-1 : Int) + c3_depth)) ∧ (((c2_node = (c3_node / (2 : Int))) ∧ (c2_sign = (0 : Int))) ∨ ((¬ (c2_node = (c3_node / (2 : Int)))) ∧ (¬ ((c3_node / (2 : Int)) ≤ c2_node))))) ∨ (shared_expr_Classification080_53 c2_depth c2_node c3_depth c3_node c3_sign))
abbrev formula_2194 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_54 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Classification080_55 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((c2_depth = c3_depth) ∧ (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ (c3_node ≤ c2_node))))) ∨ ((¬ (c2_depth = c3_depth)) ∧ (formula_2194 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev formula_2195 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_55 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Classification080_56 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (c3_kind = (0 : Int))) ∧ (((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2195 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev formula_2196 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_56 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Classification080_57 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((c2_kind = (0 : Int)) ∧ ((¬ (c3_kind = (0 : Int))) ∨ (formula_2193 c2_group c2_level c2_mode c3_group c3_level c3_mode))) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_2196 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev formula_2197 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_57 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Classification080_58 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2197 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2198 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Classification080_58 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1866 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 : Prop) : (((p0 ∧ ((p1 ∧ (((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2)) ∨ ((¬ (¬ ((¬ p2) ↔ (¬ p3)))) ∧ (((¬ p4) ∧ p5) ∨ ((¬ (¬ p4)) ∧ (((¬ p6) ∧ p7) ∨ ((¬ (¬ p6)) ∧ p8))))))) ∨ ((¬ p1) ∧ True))) ∨ ((¬ p0) ∧ ((p1 ∧ False) ∨ ((¬ p1) ∧ ((p9 ∧ (True ∧ p10)) ∨ ((¬ p9) ∧ ((p11 ∧ False) ∨ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ p15))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((p18 ∧ ((p19 ∧ p20) ∨ ((¬ p19) ∧ p21))) ∨ ((¬ p18) ∧ True)))))))))))))) ↔ ((p0 ∧ ((¬ p1) ∨ ((((¬ p2) ↔ (¬ p3)) ∧ ((p4 ∧ ((p6 ∧ (¬ (¬ p8))) ∨ ((¬ p6) ∧ (¬ (¬ p7))))) ∨ ((¬ p4) ∧ (¬ (¬ p5))))) ∨ ((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2))))) ∨ ((¬ p0) ∧ ((¬ p1) ∧ ((p9 ∧ p10) ∨ ((¬ p9) ∧ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ (¬ (¬ p15))))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((¬ p18) ∨ ((p19 ∧ p20) ∨ ((¬ p19) ∧ (¬ (¬ p21)))))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_7163 (c2_mode c3_mode : Int) : (¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ↔ (¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) := (not_congr (iff_congr (normalization_1287 c2_mode) (normalization_7047 c3_mode)))

theorem normalization_7164 (c2_level c3_level : Int) : (c2_level ≠ c3_level) ↔ (¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_7165 (c2_level c3_level : Int) : (c2_level < c3_level) ↔ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_7166 (c2_mode c3_mode : Int) : (c2_mode ≠ c3_mode) ↔ (¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_7167 (c2_mode c3_mode : Int) : (c2_mode < c3_mode) ↔ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)) := by
  omega

theorem normalization_7168 (c2_group c3_group : Int) : (c2_group < c3_group) ↔ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Classification080_59 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (((¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))))) ∧ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))
theorem normalization_7169 (c2_group c2_mode c3_group c3_mode : Int) : (((c2_mode ≠ c3_mode) ∧ (c2_mode < c3_mode)) ∨ ((¬ (c2_mode ≠ c3_mode)) ∧ (c2_group < c3_group))) ↔ (shared_expr_Classification080_59 c2_group c2_mode c3_group c3_mode) := (or_congr (and_congr (normalization_7166 c2_mode c3_mode) (normalization_7167 c2_mode c3_mode)) (and_congr (not_congr (normalization_7166 c2_mode c3_mode)) (normalization_7168 c2_group c3_group)))

abbrev shared_expr_Classification080_60 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification080_59 c2_group c2_mode c3_group c3_mode)))
theorem normalization_7170 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (((c2_level ≠ c3_level) ∧ (c2_level < c3_level)) ∨ ((¬ (c2_level ≠ c3_level)) ∧ (((c2_mode ≠ c3_mode) ∧ (c2_mode < c3_mode)) ∨ ((¬ (c2_mode ≠ c3_mode)) ∧ (c2_group < c3_group))))) ↔ (shared_expr_Classification080_60 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7164 c2_level c3_level) (normalization_7165 c2_level c3_level)) (and_congr (not_congr (normalization_7164 c2_level c3_level)) (normalization_7169 c2_group c2_mode c3_group c3_mode)))

abbrev shared_expr_Classification080_61 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))) ∨ ((¬ (¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Classification080_60 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem normalization_7171 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2187 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification080_61 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7163 c2_mode c3_mode) (normalization_1287 c2_mode)) (and_congr (not_congr (normalization_7163 c2_mode c3_mode)) (normalization_7170 c2_group c2_level c2_mode c3_group c3_level c3_mode)))

abbrev shared_expr_Classification080_62 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification080_61 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ True))
theorem normalization_7172 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : (((c3_kind = (0 : Int)) ∧ (formula_2187 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ (c3_kind = (0 : Int))) ∧ True)) ↔ (shared_expr_Classification080_62 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := (or_congr (and_congr (normalization_6540 c3_kind) (normalization_7171 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_6540 c3_kind)) (normalization_145)))

theorem normalization_7173 (c3_kind : Int) : (True ∧ (c3_kind = (1 : Int))) ↔ (True ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) := (and_congr (normalization_145) (normalization_6546 c3_kind))

theorem normalization_7174 (c2_depth c3_depth : Int) : (c2_depth = c3_depth) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_7175 (c2_node c3_node : Int) : (c2_node = c3_node) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_7176 (c2_sign c3_sign : Int) : ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) := (and_congr (normalization_662 c2_sign) (normalization_6554 c3_sign))

theorem normalization_7177 (c2_node c3_node : Int) : (c2_node < c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Classification080_63 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification080_64 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification080_63 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
theorem normalization_7178 (c2_node c2_sign c3_node c3_sign : Int) : (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (c2_node < c3_node))) ↔ (shared_expr_Classification080_64 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_7175 c2_node c3_node) (normalization_7176 c2_sign c3_sign)) (and_congr (not_congr (normalization_7175 c2_node c3_node)) (normalization_7177 c2_node c3_node)))

theorem normalization_7179 (c2_depth c3_depth : Int) : ((c2_depth + (1 : Int)) = c3_depth) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_7180 (c2_node c3_node : Int) : (c2_node = (c3_node / (2 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_7181 (c2_node c3_node : Int) : (c2_node < (c3_node / (2 : Int))) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

abbrev shared_expr_Classification080_65 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification080_66 (c2_node c2_sign c3_node : Int) : Prop := ((((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Classification080_65 c2_node c3_node))
theorem normalization_7182 (c2_node c2_sign c3_node : Int) : (((c2_node = (c3_node / (2 : Int))) ∧ (c2_sign = (0 : Int))) ∨ ((¬ (c2_node = (c3_node / (2 : Int)))) ∧ (c2_node < (c3_node / (2 : Int))))) ↔ (shared_expr_Classification080_66 c2_node c2_sign c3_node) := (or_congr (and_congr (normalization_7180 c2_node c3_node) (normalization_662 c2_sign)) (and_congr (not_congr (normalization_7180 c2_node c3_node)) (normalization_7181 c2_node c3_node)))

theorem normalization_7183 (c2_depth c3_depth : Int) : ((c3_depth + (1 : Int)) = c2_depth) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_7184 (c2_node c3_node : Int) : (c3_node = (c2_node / (2 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_7185 (c2_node c3_node : Int) : ((c2_node / (2 : Int)) < c3_node) ↔ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Classification080_67 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
abbrev shared_expr_Classification080_68 (c2_node c3_node c3_sign : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification080_67 c2_node c3_node))
theorem normalization_7186 (c2_node c3_node c3_sign : Int) : (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ ((c2_node / (2 : Int)) < c3_node))) ↔ (shared_expr_Classification080_68 c2_node c3_node c3_sign) := (or_congr (and_congr (normalization_7184 c2_node c3_node) (normalization_6554 c3_sign)) (and_congr (not_congr (normalization_7184 c2_node c3_node)) (normalization_7185 c2_node c3_node)))

abbrev shared_expr_Classification080_69 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∧ (shared_expr_Classification080_68 c2_node c3_node c3_sign)) ∨ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) ∧ True))
theorem normalization_7187 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (formula_2188 c2_depth c2_node c3_depth c3_node c3_sign) ↔ (shared_expr_Classification080_69 c2_depth c2_node c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7183 c2_depth c3_depth) (normalization_7186 c2_node c3_node c3_sign)) (and_congr (not_congr (normalization_7183 c2_depth c3_depth)) (normalization_145)))

abbrev shared_expr_Classification080_70 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification080_66 c2_node c2_sign c3_node)) ∨ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Classification080_69 c2_depth c2_node c3_depth c3_node c3_sign)))
theorem normalization_7188 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2189 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification080_70 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7179 c2_depth c3_depth) (normalization_7182 c2_node c2_sign c3_node)) (and_congr (not_congr (normalization_7179 c2_depth c3_depth)) (normalization_7187 c2_depth c2_node c3_depth c3_node c3_sign)))

abbrev shared_expr_Classification080_71 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification080_70 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
abbrev shared_expr_Classification080_72 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification080_64 c2_node c2_sign c3_node c3_sign)) ∨ (shared_expr_Classification080_71 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
theorem normalization_7189 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2190 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification080_72 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7174 c2_depth c3_depth) (normalization_7178 c2_node c2_sign c3_node c3_sign)) (and_congr (not_congr (normalization_7174 c2_depth c3_depth)) (normalization_7188 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

abbrev shared_expr_Classification080_73 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ∧ False) ∨ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification080_72 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
theorem normalization_7190 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((c3_kind = (2 : Int)) ∧ False) ∨ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2190 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))) ↔ (shared_expr_Classification080_73 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_6545 c3_kind) (normalization_147)) (and_congr (not_congr (normalization_6545 c3_kind)) (normalization_7189 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

abbrev shared_expr_Classification080_74 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ (True ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))))) ∨ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification080_73 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_7191 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2191 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Classification080_74 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_659 c2_kind) (normalization_7173 c3_kind)) (and_congr (not_congr (normalization_659 c2_kind)) (normalization_7190 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Classification080_75 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ False) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification080_74 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_7192 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((c3_kind = (0 : Int)) ∧ False) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2191 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))) ↔ (shared_expr_Classification080_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_6540 c3_kind) (normalization_147)) (and_congr (not_congr (normalization_6540 c3_kind)) (normalization_7191 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Classification080_76 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification080_62 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification080_75 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_7193 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2192 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification080_76 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (or_congr (and_congr (normalization_652 c2_kind) (normalization_7172 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) (and_congr (not_congr (normalization_652 c2_kind)) (normalization_7192 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

theorem normalization_7194 (c3_kind : Int) : (¬ (c3_kind = (0 : Int))) ↔ (¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) := (not_congr (normalization_6540 c3_kind))

theorem normalization_7195 (c2_mode c3_mode : Int) : ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ↔ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) := (iff_congr (normalization_1287 c2_mode) (normalization_7047 c3_mode))

theorem normalization_7196 (c2_level c3_level : Int) : (c2_level = c3_level) ↔ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_7197 (c2_mode c3_mode : Int) : (c2_mode = c3_mode) ↔ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_7198 (c2_group c3_group : Int) : (c3_group ≤ c2_group) ↔ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7199 (c2_group c3_group : Int) : (¬ (c3_group ≤ c2_group)) ↔ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_7198 c2_group c3_group))

theorem normalization_7200 (c2_mode c3_mode : Int) : (c3_mode ≤ c2_mode) ↔ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7201 (c2_mode c3_mode : Int) : (¬ (c3_mode ≤ c2_mode)) ↔ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_7200 c2_mode c3_mode))

abbrev shared_expr_Classification080_77 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (((((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))))
theorem normalization_7202 (c2_group c2_mode c3_group c3_mode : Int) : (((c2_mode = c3_mode) ∧ (¬ (c3_group ≤ c2_group))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ (c3_mode ≤ c2_mode)))) ↔ (shared_expr_Classification080_77 c2_group c2_mode c3_group c3_mode) := (or_congr (and_congr (normalization_7197 c2_mode c3_mode) (normalization_7199 c2_group c3_group)) (and_congr (not_congr (normalization_7197 c2_mode c3_mode)) (normalization_7201 c2_mode c3_mode)))

theorem normalization_7203 (c2_level c3_level : Int) : (c3_level ≤ c2_level) ↔ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7204 (c2_level c3_level : Int) : (¬ (c3_level ≤ c2_level)) ↔ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_7203 c2_level c3_level))

abbrev shared_expr_Classification080_78 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification080_77 c2_group c2_mode c3_group c3_mode)) ∨ ((¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))))
theorem normalization_7205 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (((c2_level = c3_level) ∧ (((c2_mode = c3_mode) ∧ (¬ (c3_group ≤ c2_group))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ (c3_mode ≤ c2_mode))))) ∨ ((¬ (c2_level = c3_level)) ∧ (¬ (c3_level ≤ c2_level)))) ↔ (shared_expr_Classification080_78 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7196 c2_level c3_level) (normalization_7202 c2_group c2_mode c3_group c3_mode)) (and_congr (not_congr (normalization_7196 c2_level c3_level)) (normalization_7204 c2_level c3_level)))

abbrev shared_expr_Classification080_79 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification080_78 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
theorem normalization_7206 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2193 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Classification080_79 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_7195 c2_mode c3_mode) (normalization_7205 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_7195 c2_mode c3_mode)) (normalization_1287 c2_mode)))

theorem normalization_7207 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((¬ (c3_kind = (0 : Int))) ∨ (formula_2193 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification080_79 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (or_congr (normalization_7194 c3_kind) (normalization_7206 c2_group c2_level c2_mode c3_group c3_level c3_mode))

theorem normalization_7208 (c3_kind : Int) : (¬ (c3_kind = (2 : Int))) ↔ (¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) := (not_congr (normalization_6545 c3_kind))

theorem normalization_7209 (c2_node c3_node : Int) : (c3_node ≤ c2_node) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7210 (c2_node c3_node : Int) : (¬ (c3_node ≤ c2_node)) ↔ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7209 c2_node c3_node))

abbrev shared_expr_Classification080_80 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Classification080_63 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_7211 (c2_node c2_sign c3_node c3_sign : Int) : (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ (c3_node ≤ c2_node)))) ↔ (shared_expr_Classification080_80 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_7175 c2_node c3_node) (normalization_7176 c2_sign c3_sign)) (and_congr (not_congr (normalization_7175 c2_node c3_node)) (normalization_7210 c2_node c3_node)))

theorem normalization_7212 (c2_depth c3_depth : Int) : (c2_depth = ((-1 : Int) + c3_depth)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_7213 (c2_node c3_node : Int) : ((c3_node / (2 : Int)) ≤ c2_node) ↔ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_7214 (c2_node c3_node : Int) : (¬ ((c3_node / (2 : Int)) ≤ c2_node)) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_7213 c2_node c3_node))

theorem normalization_7215 (c2_node c2_sign c3_node : Int) : (((c2_node = (c3_node / (2 : Int))) ∧ (c2_sign = (0 : Int))) ∨ ((¬ (c2_node = (c3_node / (2 : Int)))) ∧ (¬ ((c3_node / (2 : Int)) ≤ c2_node)))) ↔ (shared_expr_Classification080_66 c2_node c2_sign c3_node) := (or_congr (and_congr (normalization_7180 c2_node c3_node) (normalization_662 c2_sign)) (and_congr (not_congr (normalization_7180 c2_node c3_node)) (normalization_7214 c2_node c3_node)))

theorem normalization_7216 (c2_depth c3_depth : Int) : (c3_depth = ((-1 : Int) + c2_depth)) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_7217 (c2_depth c3_depth : Int) : (¬ (c3_depth = ((-1 : Int) + c2_depth))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) := (not_congr (normalization_7216 c2_depth c3_depth))

theorem normalization_7218 (c2_node c3_node : Int) : (c3_node ≤ (c2_node / (2 : Int))) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_7219 (c2_node c3_node : Int) : (¬ (c3_node ≤ (c2_node / (2 : Int)))) ↔ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_7218 c2_node c3_node))

abbrev shared_expr_Classification080_81 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification080_82 (c2_node c3_node c3_sign : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification080_81 c2_node c3_node))
theorem normalization_7220 (c2_node c3_node c3_sign : Int) : (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ (¬ (c3_node ≤ (c2_node / (2 : Int)))))) ↔ (shared_expr_Classification080_82 c2_node c3_node c3_sign) := (or_congr (and_congr (normalization_7184 c2_node c3_node) (normalization_6554 c3_sign)) (and_congr (not_congr (normalization_7184 c2_node c3_node)) (normalization_7219 c2_node c3_node)))

theorem normalization_7221 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : ((¬ (c3_depth = ((-1 : Int) + c2_depth))) ∨ (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ (¬ (c3_node ≤ (c2_node / (2 : Int))))))) ↔ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Classification080_82 c2_node c3_node c3_sign)) := (or_congr (normalization_7217 c2_depth c3_depth) (normalization_7220 c2_node c3_node c3_sign))

abbrev shared_expr_Classification080_83 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Classification080_82 c2_node c3_node c3_sign)))
abbrev shared_expr_Classification080_84 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification080_66 c2_node c2_sign c3_node)) ∨ (shared_expr_Classification080_83 c2_depth c2_node c3_depth c3_node c3_sign))
theorem normalization_7222 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2194 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification080_84 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7212 c2_depth c3_depth) (normalization_7215 c2_node c2_sign c3_node)) (and_congr (not_congr (normalization_7212 c2_depth c3_depth)) (normalization_7221 c2_depth c2_node c3_depth c3_node c3_sign)))

abbrev shared_expr_Classification080_85 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification080_84 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
abbrev shared_expr_Classification080_86 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification080_80 c2_node c2_sign c3_node c3_sign)) ∨ (shared_expr_Classification080_85 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))
theorem normalization_7223 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2195 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Classification080_86 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_7174 c2_depth c3_depth) (normalization_7211 c2_node c2_sign c3_node c3_sign)) (and_congr (not_congr (normalization_7174 c2_depth c3_depth)) (normalization_7222 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

theorem normalization_7224 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : ((¬ (c3_kind = (2 : Int))) ∧ (formula_2195 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification080_86 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (and_congr (normalization_7208 c3_kind) (normalization_7223 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

abbrev shared_expr_Classification080_87 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification080_86 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev shared_expr_Classification080_88 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) ∨ (shared_expr_Classification080_87 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7225 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2195 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))) ↔ (shared_expr_Classification080_88 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_659 c2_kind) (normalization_6546 c3_kind)) (and_congr (not_congr (normalization_659 c2_kind)) (normalization_7224 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

theorem normalization_7226 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2196 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification080_88 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := (and_congr (normalization_7194 c3_kind) (normalization_7225 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

abbrev shared_expr_Classification080_89 (c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification080_79 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
abbrev shared_expr_Classification080_90 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification080_88 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev shared_expr_Classification080_91 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification080_89 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Classification080_90 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_7227 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2197 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification080_91 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (or_congr (and_congr (normalization_652 c2_kind) (normalization_7207 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) (and_congr (not_congr (normalization_652 c2_kind)) (normalization_7226 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Classification080_92 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Classification080_76 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification080_91 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
theorem normalization_7228 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2198 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Classification080_92 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_7193 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_7227 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_5093 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2198 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1866 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((c2_mode) ≤ (3 : Int)) ((c3_mode) ≤ (3 : Int)) (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Classification080_66 c2_node c2_sign c3_node) ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_7228 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

end H4Formal.Generated.Classification
