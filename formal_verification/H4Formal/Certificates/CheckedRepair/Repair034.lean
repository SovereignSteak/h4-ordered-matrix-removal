import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair033

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair034_0 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((c0_kind = (1 : Int)) ∧ (c0_mode = (0 : Int)) ∧ (c0_level = (0 : Int)) ∧ (c0_group = (0 : Int)) ∧ (c0_depth ≥ (0 : Int)) ∧ (c0_depth ≤ h) ∧ (c0_node ≥ (0 : Int)) ∧ ((c0_depth = (0 : Int)) → (c0_node = (0 : Int))) ∧ (((c0_depth = h) ∧ (c0_sign = (2 : Int))) ∨ ((¬ (c0_depth = h)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (1 : Int))))))
abbrev formula_780 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_0 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

abbrev shared_expr_Repair034_1 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((c0_kind = (1 : Int)) ∧ (c0_mode = (0 : Int)) ∧ (c0_level = (0 : Int)) ∧ (c0_group = (0 : Int)) ∧ (c0_depth ≥ (0 : Int)) ∧ (c0_depth ≤ h) ∧ (c0_node ≥ (0 : Int)) ∧ ((¬ (c0_depth = (0 : Int))) ∨ (c0_node = (0 : Int))) ∧ (((c0_depth = h) ∧ (c0_sign = (2 : Int))) ∨ ((¬ (c0_depth = h)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (1 : Int))))))
abbrev formula_781 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_1 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

theorem normalized_730 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : ((p0 ∧ p1 ∧ p2 ∧ p3 ∧ (¬ p4) ∧ p5 ∧ (¬ p6) ∧ (p7 → p8) ∧ p9) ↔ (p0 ∧ p1 ∧ p2 ∧ p3 ∧ (¬ p4) ∧ p5 ∧ (¬ p6) ∧ ((¬ p7) ∨ p8) ∧ p9)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2877 (c0_level : Int) : (c0_level = (0 : Int)) ↔ (((c0_level) ≤ (0 : Int)) ∧ (¬ ((c0_level) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2878 (c0_group : Int) : (c0_group = (0 : Int)) ↔ (((c0_group) ≤ (0 : Int)) ∧ (¬ ((c0_group) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2879 (c0_depth : Int) : (c0_depth ≥ (0 : Int)) ↔ (¬ ((c0_depth) ≤ (-1 : Int))) := by
  omega

theorem normalization_2880 (c0_depth h : Int) : (c0_depth ≤ h) ↔ ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) := by
  omega

theorem normalization_2881 (c0_node : Int) : (c0_node ≥ (0 : Int)) ↔ (¬ ((c0_node) ≤ (-1 : Int))) := by
  omega

theorem normalization_2882 (c0_depth c0_node : Int) : ((c0_depth = (0 : Int)) → (c0_node = (0 : Int))) ↔ ((((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) → (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int))))) := (imp_congr (normalization_2870 c0_depth) (normalization_2871 c0_node))

theorem normalization_2883 (c0_sign : Int) : ((c0_sign = (0 : Int)) ∨ (c0_sign = (1 : Int))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int))))) := (or_congr (normalization_144 c0_sign) (normalization_151 c0_sign))

abbrev shared_expr_Repair034_2 (c0_depth c0_sign h : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair034_3 (c0_depth c0_sign h : Int) : Prop := (((((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∨ (shared_expr_Repair034_2 c0_depth c0_sign h))
theorem normalization_2884 (c0_depth c0_sign h : Int) : (((c0_depth = h) ∧ (c0_sign = (2 : Int))) ∨ ((¬ (c0_depth = h)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (1 : Int))))) ↔ (shared_expr_Repair034_3 c0_depth c0_sign h) := (or_congr (and_congr (normalization_219 c0_depth h) (normalization_145 c0_sign)) (and_congr (not_congr (normalization_219 c0_depth h)) (normalization_2883 c0_sign)))

abbrev shared_expr_Repair034_4 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_mode) ≤ (0 : Int)) ∧ (¬ ((c0_mode) ≤ (-1 : Int)))) ∧ (((c0_level) ≤ (0 : Int)) ∧ (¬ ((c0_level) ≤ (-1 : Int)))) ∧ (((c0_group) ≤ (0 : Int)) ∧ (¬ ((c0_group) ≤ (-1 : Int)))) ∧ (¬ ((c0_depth) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int))) ∧ ((((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) → (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_3 c0_depth c0_sign h))
theorem normalization_2885 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_780 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_4 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (and_congr (normalization_142 c0_kind) (and_congr (normalization_179 c0_mode) (and_congr (normalization_2877 c0_level) (and_congr (normalization_2878 c0_group) (and_congr (normalization_2879 c0_depth) (and_congr (normalization_2880 c0_depth h) (and_congr (normalization_2881 c0_node) (and_congr (normalization_2882 c0_depth c0_node) (normalization_2884 c0_depth c0_sign h)))))))))

theorem normalization_2886 (c0_depth : Int) : (¬ (c0_depth = (0 : Int))) ↔ (¬ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int))))) := (not_congr (normalization_2870 c0_depth))

theorem normalization_2887 (c0_depth c0_node : Int) : ((¬ (c0_depth = (0 : Int))) ∨ (c0_node = (0 : Int))) ↔ ((¬ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int))))) ∨ (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int))))) := (or_congr (normalization_2886 c0_depth) (normalization_2871 c0_node))

abbrev shared_expr_Repair034_5 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_mode) ≤ (0 : Int)) ∧ (¬ ((c0_mode) ≤ (-1 : Int)))) ∧ (((c0_level) ≤ (0 : Int)) ∧ (¬ ((c0_level) ≤ (-1 : Int)))) ∧ (((c0_group) ≤ (0 : Int)) ∧ (¬ ((c0_group) ≤ (-1 : Int)))) ∧ (¬ ((c0_depth) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int))) ∧ ((¬ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int))))) ∨ (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_3 c0_depth c0_sign h))
theorem normalization_2888 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_781 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_5 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (and_congr (normalization_142 c0_kind) (and_congr (normalization_179 c0_mode) (and_congr (normalization_2877 c0_level) (and_congr (normalization_2878 c0_group) (and_congr (normalization_2879 c0_depth) (and_congr (normalization_2880 c0_depth h) (and_congr (normalization_2881 c0_node) (and_congr (normalization_2887 c0_depth c0_node) (normalization_2884 c0_depth c0_sign h)))))))))

theorem normalization_2889 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_780 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_781 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ ((shared_expr_Repair034_4 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_5 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (iff_congr (normalization_2885 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2888 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

-- Checked replay of rewrite.
theorem replay_2115 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_780 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_781 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  classical
  have ht := (normalized_730 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) (((c0_mode) ≤ (0 : Int)) ∧ (¬ ((c0_mode) ≤ (-1 : Int)))) (((c0_level) ≤ (0 : Int)) ∧ (¬ ((c0_level) ≤ (-1 : Int)))) (((c0_group) ≤ (0 : Int)) ∧ (¬ ((c0_group) ≤ (-1 : Int)))) ((c0_depth) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c0_node) ≤ (-1 : Int)) (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int)))) (shared_expr_Repair034_3 c0_depth c0_sign h))
  have hn := ht
  exact Iff.mpr (normalization_2889 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) hn

abbrev shared_expr_Repair034_6 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((formula_778 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (formula_780 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ ((c0_kind = (2 : Int)) ∧ (c0_mode = (0 : Int)) ∧ (c0_level = (0 : Int)) ∧ (c0_group = (0 : Int)) ∧ (c0_depth = (0 : Int)) ∧ (c0_node = (0 : Int)) ∧ (c0_sign = (0 : Int))))
abbrev formula_782 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_6 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

abbrev shared_expr_Repair034_7 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((formula_779 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (formula_781 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ ((c0_kind = (2 : Int)) ∧ (c0_mode = (0 : Int)) ∧ (c0_level = (0 : Int)) ∧ (c0_group = (0 : Int)) ∧ (c0_depth = (0 : Int)) ∧ (c0_node = (0 : Int)) ∧ (c0_sign = (0 : Int))))
abbrev formula_783 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_7 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

theorem normalized_731 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ p1) ∧ (p2 ↔ p3)) → ((p0 ∨ p2 ∨ p4) ↔ (p1 ∨ p3 ∨ p4))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair034_8 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : Prop := ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c0_mode) ≤ (0 : Int)) ∧ (¬ ((c0_mode) ≤ (-1 : Int)))) ∧ (((c0_level) ≤ (0 : Int)) ∧ (¬ ((c0_level) ≤ (-1 : Int)))) ∧ (((c0_group) ≤ (0 : Int)) ∧ (¬ ((c0_group) ≤ (-1 : Int)))) ∧ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) ∧ (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))))
theorem normalization_2890 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : ((c0_kind = (2 : Int)) ∧ (c0_mode = (0 : Int)) ∧ (c0_level = (0 : Int)) ∧ (c0_group = (0 : Int)) ∧ (c0_depth = (0 : Int)) ∧ (c0_node = (0 : Int)) ∧ (c0_sign = (0 : Int))) ↔ (shared_expr_Repair034_8 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) := (and_congr (normalization_141 c0_kind) (and_congr (normalization_179 c0_mode) (and_congr (normalization_2877 c0_level) (and_congr (normalization_2878 c0_group) (and_congr (normalization_2870 c0_depth) (and_congr (normalization_2871 c0_node) (normalization_144 c0_sign)))))))

abbrev shared_expr_Repair034_9 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (¬ ((c0_mode) ≤ (-1 : Int))) ∧ ((c0_mode) ≤ (5 : Int)) ∧ (¬ ((c0_level) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∨ (((c0_group) ≤ (2 : Int)) ∧ (¬ ((c0_group) ≤ (1 : Int))))) ∧ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) ∧ (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))))
abbrev shared_expr_Repair034_10 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((shared_expr_Repair034_9 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (shared_expr_Repair034_4 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (shared_expr_Repair034_8 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign))
theorem normalization_2891 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_10 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (or_congr (normalization_2872 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (or_congr (normalization_2885 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2890 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign)))

abbrev shared_expr_Repair034_11 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (¬ ((c0_mode) ≤ (-1 : Int))) ∧ (¬ (¬ ((c0_mode) ≤ (5 : Int)))) ∧ (¬ ((c0_level) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∨ (((c0_group) ≤ (2 : Int)) ∧ (¬ ((c0_group) ≤ (1 : Int))))) ∧ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) ∧ (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))))
abbrev shared_expr_Repair034_12 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((shared_expr_Repair034_11 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (shared_expr_Repair034_5 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (shared_expr_Repair034_8 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign))
theorem normalization_2892 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_783 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_12 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (or_congr (normalization_2875 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (or_congr (normalization_2888 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2890 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign)))

theorem normalization_2893 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_783 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ ((shared_expr_Repair034_10 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_12 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (iff_congr (normalization_2891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2892 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

-- Checked replay of monotonicity.
theorem replay_2116 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_783 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  classical
  have ht := (normalized_731 (shared_expr_Repair034_9 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (shared_expr_Repair034_11 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (shared_expr_Repair034_4 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (shared_expr_Repair034_5 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (shared_expr_Repair034_8 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign))
  have n0 : ((shared_expr_Repair034_9 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_11 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
    exact Iff.mp (normalization_2876 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (replay_2114 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)
  have n1 : ((shared_expr_Repair034_4 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_5 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
    exact Iff.mp (normalization_2889 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (replay_2115 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2893 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) hn

abbrev shared_expr_Repair034_13 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (((c0_kind = (2 : Int)) ∧ (c0_mode = (0 : Int)) ∧ (c0_level = (0 : Int)) ∧ (c0_group = (0 : Int)) ∧ (c0_depth = (0 : Int)) ∧ (c0_node = (0 : Int)) ∧ (c0_sign = (0 : Int))) ∨ (formula_779 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (formula_781 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))
abbrev formula_784 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_13 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

theorem normalized_732 (p0 p1 p2 : Prop) : ((p0 ∨ p1 ∨ p2) ↔ (p2 ∨ p0 ∨ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair034_14 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((shared_expr_Repair034_8 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) ∨ (shared_expr_Repair034_11 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (shared_expr_Repair034_5 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))
theorem normalization_2894 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (or_congr (normalization_2890 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) (or_congr (normalization_2875 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2888 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)))

theorem normalization_2895 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_783 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ ((shared_expr_Repair034_12 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (iff_congr (normalization_2892 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2894 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

-- Checked replay of rewrite.
theorem replay_2117 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_783 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  classical
  have ht := (normalized_732 (shared_expr_Repair034_11 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (shared_expr_Repair034_5 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (shared_expr_Repair034_8 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign))
  have hn := ht
  exact Iff.mpr (normalization_2895 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) hn

theorem normalized_733 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2896 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ ((shared_expr_Repair034_10 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (iff_congr (normalization_2891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2894 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

-- Checked replay of trans.
theorem replay_2118 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  classical
  have ht := (normalized_733 (shared_expr_Repair034_10 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (shared_expr_Repair034_12 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))
  have n0 : ((shared_expr_Repair034_10 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_12 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
    exact Iff.mp (normalization_2893 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (replay_2116 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)
  have n1 : ((shared_expr_Repair034_12 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
    exact Iff.mp (normalization_2895 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (replay_2117 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2896 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) hn

-- Checked replay of mp.
theorem replay_2119 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) : (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := by
  exact Iff.mp (replay_2118 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) i154

theorem normalized_734 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2897 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ ((shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (iff_congr (normalization_2894 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2894 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

-- Checked replay of rewrite.
theorem replay_2120 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  classical
  have ht := (normalized_734 (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))
  have hn := ht
  exact Iff.mpr (normalization_2897 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) hn

-- Checked replay of mp.
theorem replay_2121 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) : (formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := by
  exact Iff.mp (replay_2120 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (replay_2119 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154)

abbrev shared_expr_Repair034_15 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((c0_kind = (0 : Int)) ∧ (c0_mode ≥ (0 : Int)) ∧ (¬ (c0_mode ≥ (6 : Int))) ∧ (c0_level ≥ (1 : Int)) ∧ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ∧ ((c0_group = (1 : Int)) ∨ (c0_group = (2 : Int))) ∧ (c0_depth = (0 : Int)) ∧ (c0_node = (0 : Int)) ∧ (c0_sign = (0 : Int)))
abbrev formula_785 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_15 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

abbrev shared_expr_Repair034_16 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((c0_kind = (1 : Int)) ∧ (c0_mode = (0 : Int)) ∧ (c0_level = (0 : Int)) ∧ (c0_group = (0 : Int)) ∧ (c0_depth ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ∧ (c0_node ≥ (0 : Int)) ∧ ((¬ (c0_depth = (0 : Int))) ∨ (c0_node = (0 : Int))) ∧ (((c0_depth = h) ∧ (c0_sign = (2 : Int))) ∨ ((¬ (c0_depth = h)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (1 : Int))))))
abbrev formula_786 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_16 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

abbrev shared_expr_Repair034_17 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (((c0_kind = (2 : Int)) ∧ (c0_mode = (0 : Int)) ∧ (c0_level = (0 : Int)) ∧ (c0_group = (0 : Int)) ∧ (c0_depth = (0 : Int)) ∧ (c0_node = (0 : Int)) ∧ (c0_sign = (0 : Int))) ∨ (formula_785 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (formula_786 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))
abbrev formula_787 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_17 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

theorem normalized_735 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2898 (c0_mode : Int) : (c0_mode ≥ (6 : Int)) ↔ (¬ ((c0_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_2899 (c0_mode : Int) : (¬ (c0_mode ≥ (6 : Int))) ↔ (¬ (¬ ((c0_mode) ≤ (5 : Int)))) := (not_congr (normalization_2898 c0_mode))

theorem normalization_2900 (c0_level h : Int) : ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) := by
  omega

theorem normalization_2901 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_785 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_11 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (and_congr (normalization_134 c0_kind) (and_congr (normalization_628 c0_mode) (and_congr (normalization_2899 c0_mode) (and_congr (normalization_2866 c0_level) (and_congr (normalization_2900 c0_level h) (and_congr (normalization_2869 c0_group) (and_congr (normalization_2870 c0_depth) (and_congr (normalization_2871 c0_node) (normalization_144 c0_sign)))))))))

theorem normalization_2902 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_786 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_5 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (and_congr (normalization_142 c0_kind) (and_congr (normalization_179 c0_mode) (and_congr (normalization_2877 c0_level) (and_congr (normalization_2878 c0_group) (and_congr (normalization_2879 c0_depth) (and_congr (normalization_566 c0_depth h) (and_congr (normalization_2881 c0_node) (and_congr (normalization_2887 c0_depth c0_node) (normalization_2884 c0_depth c0_sign h)))))))))

theorem normalization_2903 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_787 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (or_congr (normalization_2890 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) (or_congr (normalization_2901 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2902 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)))

theorem normalization_2904 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_787 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ ((shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (iff_congr (normalization_2894 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2903 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

-- Checked replay of rewrite.
theorem replay_2122 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_787 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  classical
  have ht := (normalized_735 (shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))
  have hn := ht
  exact Iff.mpr (normalization_2904 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) hn

-- Checked replay of mp.
theorem replay_2123 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) : (formula_787 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := by
  exact Iff.mp (replay_2122 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (replay_2121 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154)

abbrev shared_expr_Repair034_18 (c0_depth c0_sign h : Int) : Prop := (((¬ ((h + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))) ∧ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int)))))))
abbrev shared_expr_Repair034_19 (c0_depth c0_sign h : Int) : Prop := ((shared_expr_Repair034_18 c0_depth c0_sign h) ∨ ((¬ ((¬ ((h + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_depth)) ≤ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))))
abbrev formula_788 (c0_depth c0_sign h : Int) : Prop := (shared_expr_Repair034_19 c0_depth c0_sign h)

abbrev shared_expr_Repair034_20 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (c0_level ≤ (0 : Int))) ∨ (¬ (c0_level ≥ (0 : Int))) ∨ (¬ (c0_group ≤ (0 : Int))) ∨ (¬ (c0_group ≥ (0 : Int))) ∨ (¬ (c0_depth ≥ (0 : Int))) ∨ (¬ (c0_node ≥ (0 : Int))) ∨ (¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((¬ (c0_depth ≤ (0 : Int))) ∨ (¬ (c0_depth ≥ (0 : Int))) ∨ (¬ ((¬ (c0_node ≤ (0 : Int))) ∨ (¬ (c0_node ≥ (0 : Int))))))) ∨ (¬ (formula_788 c0_depth c0_sign h)))
abbrev formula_789 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_20 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

abbrev shared_expr_Repair034_21 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((¬ (formula_777 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign)) ∨ (¬ (formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ∨ (¬ (formula_789 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)))
abbrev formula_790 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair034_21 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

theorem normalized_736 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p14 ∧ (¬ p15)) ∧ (¬ p3) ∧ (¬ (¬ p16)) ∧ (¬ p4) ∧ p17 ∧ ((p18 ∧ (¬ p6)) ∨ (p19 ∧ (¬ p18))) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p1 ∧ (¬ p14)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (¬ p9) ∧ p20 ∧ (¬ p11) ∧ ((¬ (p8 ∧ (¬ p9))) ∨ (p10 ∧ (¬ p11))) ∧ (((p20 ∧ (¬ p21)) ∧ (p22 ∧ (¬ p23))) ∨ ((¬ (p20 ∧ (¬ p21))) ∧ ((p12 ∧ (¬ p13)) ∨ (p23 ∧ (¬ p12))))))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ p10) ∨ (¬ (¬ p11)) ∨ (¬ p12) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p16) ∨ (¬ (¬ p3)) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ p10) ∨ (¬ (¬ p11)) ∨ (¬ p12) ∨ (¬ (¬ p13)) ∨ (¬ p14) ∨ (¬ (¬ p15)) ∨ (¬ (¬ p4)) ∨ (¬ p17) ∨ (¬ ((¬ ((¬ p18) ∨ (¬ (¬ p6)))) ∨ (¬ ((¬ p19) ∨ (¬ (¬ p18)))))))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ (¬ p9)) ∨ (¬ (¬ p11)) ∨ (¬ p1) ∨ (¬ (¬ p14)) ∨ (¬ p20) ∨ (¬ ((¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ ((¬ p10) ∨ (¬ (¬ p11)))))) ∨ (¬ ((((¬ p20) ∨ (¬ (¬ p21))) ∧ ((¬ ((¬ p12) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p23) ∨ (¬ (¬ p12)))))) ∨ ((¬ ((¬ p20) ∨ (¬ (¬ p21)))) ∧ (¬ ((¬ p22) ∨ (¬ (¬ p23))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2905 (c0_level : Int) : (c0_level ≤ (0 : Int)) ↔ ((c0_level) ≤ (0 : Int)) := by
  omega

theorem normalization_2906 (c0_level : Int) : (¬ (c0_level ≤ (0 : Int))) ↔ (¬ ((c0_level) ≤ (0 : Int))) := (not_congr (normalization_2905 c0_level))

theorem normalization_2907 (c0_level : Int) : (c0_level ≥ (0 : Int)) ↔ (¬ ((c0_level) ≤ (-1 : Int))) := by
  omega

theorem normalization_2908 (c0_level : Int) : (¬ (c0_level ≥ (0 : Int))) ↔ (¬ (¬ ((c0_level) ≤ (-1 : Int)))) := (not_congr (normalization_2907 c0_level))

theorem normalization_2909 (c0_group : Int) : (c0_group ≤ (0 : Int)) ↔ ((c0_group) ≤ (0 : Int)) := by
  omega

theorem normalization_2910 (c0_group : Int) : (¬ (c0_group ≤ (0 : Int))) ↔ (¬ ((c0_group) ≤ (0 : Int))) := (not_congr (normalization_2909 c0_group))

theorem normalization_2911 (c0_group : Int) : (c0_group ≥ (0 : Int)) ↔ (¬ ((c0_group) ≤ (-1 : Int))) := by
  omega

theorem normalization_2912 (c0_group : Int) : (¬ (c0_group ≥ (0 : Int))) ↔ (¬ (¬ ((c0_group) ≤ (-1 : Int)))) := (not_congr (normalization_2911 c0_group))

theorem normalization_2913 (c0_depth : Int) : (c0_depth ≤ (0 : Int)) ↔ ((c0_depth) ≤ (0 : Int)) := by
  omega

theorem normalization_2914 (c0_depth : Int) : (¬ (c0_depth ≤ (0 : Int))) ↔ (¬ ((c0_depth) ≤ (0 : Int))) := (not_congr (normalization_2913 c0_depth))

theorem normalization_2915 (c0_depth : Int) : (¬ (c0_depth ≥ (0 : Int))) ↔ (¬ (¬ ((c0_depth) ≤ (-1 : Int)))) := (not_congr (normalization_2879 c0_depth))

theorem normalization_2916 (c0_node : Int) : (c0_node ≤ (0 : Int)) ↔ ((c0_node) ≤ (0 : Int)) := by
  omega

theorem normalization_2917 (c0_node : Int) : (¬ (c0_node ≤ (0 : Int))) ↔ (¬ ((c0_node) ≤ (0 : Int))) := (not_congr (normalization_2916 c0_node))

theorem normalization_2918 (c0_node : Int) : (¬ (c0_node ≥ (0 : Int))) ↔ (¬ (¬ ((c0_node) ≤ (-1 : Int)))) := (not_congr (normalization_2881 c0_node))

abbrev shared_expr_Repair034_22 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : Prop := ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int)))) ∨ (¬ ((c0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (-1 : Int)))) ∨ (¬ ((c0_level) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level) ≤ (-1 : Int)))) ∨ (¬ ((c0_group) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth) ≤ (-1 : Int)))) ∨ (¬ ((c0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node) ≤ (-1 : Int)))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))
theorem normalization_2919 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : (formula_777 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) ↔ (shared_expr_Repair034_22 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) := (or_congr (normalization_477 c0_kind) (or_congr (normalization_479 c0_kind) (or_congr (normalization_627 c0_mode) (or_congr (normalization_629 c0_mode) (or_congr (normalization_2906 c0_level) (or_congr (normalization_2908 c0_level) (or_congr (normalization_2910 c0_group) (or_congr (normalization_2912 c0_group) (or_congr (normalization_2914 c0_depth) (or_congr (normalization_2915 c0_depth) (or_congr (normalization_2917 c0_node) (or_congr (normalization_2918 c0_node) (or_congr (normalization_457 c0_sign) (normalization_459 c0_sign))))))))))))))

theorem normalization_2920 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : (¬ (formula_777 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign)) ↔ (¬ (shared_expr_Repair034_22 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign)) := (not_congr (normalization_2919 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign))

theorem normalization_2921 (c0_level : Int) : (¬ (c0_level ≥ (1 : Int))) ↔ (¬ (¬ ((c0_level) ≤ (0 : Int)))) := (not_congr (normalization_2866 c0_level))

theorem normalization_2922 (c0_level h : Int) : (¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int))) := (not_congr (normalization_2900 c0_level h))

theorem normalization_2923 (c0_group : Int) : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) := (not_congr (normalization_634 c0_group))

theorem normalization_2924 (c0_group : Int) : (c0_group ≤ (2 : Int)) ↔ ((c0_group) ≤ (2 : Int)) := by
  omega

theorem normalization_2925 (c0_group : Int) : (¬ (c0_group ≤ (2 : Int))) ↔ (¬ ((c0_group) ≤ (2 : Int))) := (not_congr (normalization_2924 c0_group))

theorem normalization_2926 (c0_group : Int) : (c0_group ≥ (2 : Int)) ↔ (¬ ((c0_group) ≤ (1 : Int))) := by
  omega

theorem normalization_2927 (c0_group : Int) : (¬ (c0_group ≥ (2 : Int))) ↔ (¬ (¬ ((c0_group) ≤ (1 : Int)))) := (not_congr (normalization_2926 c0_group))

theorem normalization_2928 (c0_group : Int) : ((¬ (c0_group ≤ (2 : Int))) ∨ (¬ (c0_group ≥ (2 : Int)))) ↔ ((¬ ((c0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (1 : Int))))) := (or_congr (normalization_2925 c0_group) (normalization_2927 c0_group))

theorem normalization_2929 (c0_group : Int) : (¬ ((¬ (c0_group ≤ (2 : Int))) ∨ (¬ (c0_group ≥ (2 : Int))))) ↔ (¬ ((¬ ((c0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (1 : Int)))))) := (not_congr (normalization_2928 c0_group))

theorem normalization_2930 (c0_group : Int) : ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_group ≤ (2 : Int))) ∨ (¬ (c0_group ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (1 : Int))))))) := (or_congr (normalization_2923 c0_group) (normalization_2929 c0_group))

theorem normalization_2931 (c0_group : Int) : (¬ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_group ≤ (2 : Int))) ∨ (¬ (c0_group ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (1 : Int)))))))) := (not_congr (normalization_2930 c0_group))

abbrev shared_expr_Repair034_23 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((¬ ((c0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth) ≤ (-1 : Int)))) ∨ (¬ ((c0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node) ≤ (-1 : Int)))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_level) ≤ (0 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (1 : Int)))))))))
theorem normalization_2932 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_23 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (or_congr (normalization_2898 c0_mode) (or_congr (normalization_629 c0_mode) (or_congr (normalization_2914 c0_depth) (or_congr (normalization_2915 c0_depth) (or_congr (normalization_2917 c0_node) (or_congr (normalization_2918 c0_node) (or_congr (normalization_457 c0_sign) (or_congr (normalization_459 c0_sign) (or_congr (normalization_376 c0_kind) (or_congr (normalization_377 c0_kind) (or_congr (normalization_2921 c0_level) (or_congr (normalization_2922 c0_level h) (normalization_2931 c0_group)))))))))))))

theorem normalization_2933 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (¬ (formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ (¬ (shared_expr_Repair034_23 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (not_congr (normalization_2932 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

theorem normalization_2934 (c0_node : Int) : ((¬ (c0_node ≤ (0 : Int))) ∨ (¬ (c0_node ≥ (0 : Int)))) ↔ ((¬ ((c0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node) ≤ (-1 : Int))))) := (or_congr (normalization_2917 c0_node) (normalization_2918 c0_node))

theorem normalization_2935 (c0_node : Int) : (¬ ((¬ (c0_node ≤ (0 : Int))) ∨ (¬ (c0_node ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node) ≤ (-1 : Int)))))) := (not_congr (normalization_2934 c0_node))

theorem normalization_2936 (c0_depth c0_node : Int) : ((¬ (c0_depth ≤ (0 : Int))) ∨ (¬ (c0_depth ≥ (0 : Int))) ∨ (¬ ((¬ (c0_node ≤ (0 : Int))) ∨ (¬ (c0_node ≥ (0 : Int)))))) ↔ ((¬ ((c0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((c0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node) ≤ (-1 : Int))))))) := (or_congr (normalization_2914 c0_depth) (or_congr (normalization_2915 c0_depth) (normalization_2935 c0_node)))

theorem normalization_2937 (c0_depth c0_node : Int) : (¬ ((¬ (c0_depth ≤ (0 : Int))) ∨ (¬ (c0_depth ≥ (0 : Int))) ∨ (¬ ((¬ (c0_node ≤ (0 : Int))) ∨ (¬ (c0_node ≥ (0 : Int))))))) ↔ (¬ ((¬ ((c0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((c0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node) ≤ (-1 : Int)))))))) := (not_congr (normalization_2936 c0_depth c0_node))

theorem normalization_2938 (c0_depth h : Int) : ((¬ ((h + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) := (or_congr (normalization_567 c0_depth h) (normalization_569 c0_depth h))

theorem normalization_2939 (c0_sign : Int) : ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int))))))) := (or_congr (normalization_461 c0_sign) (normalization_495 c0_sign))

abbrev shared_expr_Repair034_24 (c0_depth c0_sign h : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int))))))))
abbrev shared_expr_Repair034_25 (c0_depth c0_sign h : Int) : Prop := ((shared_expr_Repair034_24 c0_depth c0_sign h) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
theorem normalization_2940 (c0_depth c0_sign h : Int) : (formula_788 c0_depth c0_sign h) ↔ (shared_expr_Repair034_25 c0_depth c0_sign h) := (or_congr (and_congr (normalization_2938 c0_depth h) (normalization_2939 c0_sign)) (and_congr (not_congr (normalization_2938 c0_depth h)) (normalization_467 c0_sign)))

theorem normalization_2941 (c0_depth c0_sign h : Int) : (¬ (formula_788 c0_depth c0_sign h)) ↔ (¬ (shared_expr_Repair034_25 c0_depth c0_sign h)) := (not_congr (normalization_2940 c0_depth c0_sign h))

abbrev shared_expr_Repair034_26 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((¬ ((c0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (-1 : Int)))) ∨ (¬ ((c0_level) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level) ≤ (-1 : Int)))) ∨ (¬ ((c0_group) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_depth) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node) ≤ (-1 : Int)))) ∨ (¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ ((¬ ((c0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((c0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node) ≤ (-1 : Int)))))))) ∨ (¬ (shared_expr_Repair034_25 c0_depth c0_sign h)))
theorem normalization_2942 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_789 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_26 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (or_congr (normalization_627 c0_mode) (or_congr (normalization_629 c0_mode) (or_congr (normalization_2906 c0_level) (or_congr (normalization_2908 c0_level) (or_congr (normalization_2910 c0_group) (or_congr (normalization_2912 c0_group) (or_congr (normalization_2915 c0_depth) (or_congr (normalization_2918 c0_node) (or_congr (normalization_453 c0_kind) (or_congr (normalization_455 c0_kind) (or_congr (normalization_567 c0_depth h) (or_congr (normalization_2937 c0_depth c0_node) (normalization_2941 c0_depth c0_sign h)))))))))))))

theorem normalization_2943 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (¬ (formula_789 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ (¬ (shared_expr_Repair034_26 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (not_congr (normalization_2942 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

abbrev shared_expr_Repair034_27 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((¬ (shared_expr_Repair034_22 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign)) ∨ (¬ (shared_expr_Repair034_23 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ∨ (¬ (shared_expr_Repair034_26 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)))
theorem normalization_2944 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_790 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_27 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (or_congr (normalization_2920 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) (or_congr (normalization_2933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2943 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)))

theorem normalization_2945 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_787 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_790 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ ((shared_expr_Repair034_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair034_27 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (iff_congr (normalization_2903 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2944 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

-- Checked replay of rewrite.
theorem replay_2124 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_787 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_790 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  classical
  have ht := (normalized_736 ((c0_kind) ≤ (2 : Int)) ((c0_kind) ≤ (1 : Int)) ((c0_mode) ≤ (0 : Int)) ((c0_mode) ≤ (-1 : Int)) ((c0_level) ≤ (0 : Int)) ((c0_level) ≤ (-1 : Int)) ((c0_group) ≤ (0 : Int)) ((c0_group) ≤ (-1 : Int)) ((c0_depth) ≤ (0 : Int)) ((c0_depth) ≤ (-1 : Int)) ((c0_node) ≤ (0 : Int)) ((c0_node) ≤ (-1 : Int)) ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_kind) ≤ (-1 : Int)) ((c0_mode) ≤ (5 : Int)) ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ((c0_group) ≤ (1 : Int)) ((c0_group) ≤ (2 : Int)) ((c0_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c0_sign) ≤ (2 : Int)) ((c0_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2945 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) hn

-- Checked replay of mp.
theorem replay_2125 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) : (formula_790 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := by
  exact Iff.mp (replay_2124 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (replay_2123 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154)

theorem propositional_737 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p7))))) ∨ (¬ ((((¬ p10) ∨ (¬ p13)) ∧ ((¬ ((¬ p14) ∨ (¬ p15))) ∨ (¬ ((¬ p16) ∨ (¬ p17))))) ∨ ((¬ ((¬ p10) ∨ (¬ p13))) ∧ (¬ ((¬ p18) ∨ (¬ p19))))))) ∨ p9) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2126 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_789 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (c0_kind ≥ (1 : Int))) := by
  exact (propositional_737 (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) (c0_level ≤ (0 : Int)) (c0_level ≥ (0 : Int)) (c0_group ≤ (0 : Int)) (c0_group ≥ (0 : Int)) (c0_depth ≥ (0 : Int)) (c0_node ≥ (0 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) (c0_depth ≤ (0 : Int)) (c0_node ≤ (0 : Int)) ((h + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) (c0_sign ≤ (1 : Int)) (c0_sign ≥ (1 : Int)) (c0_sign ≤ (2 : Int)) (c0_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2127 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i155 : (¬ (c0_kind ≥ (1 : Int)))) : (formula_789 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := by
  exact (Or.elim (replay_2126 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i155 t0))))

-- Checked replay of unit-resolution.
theorem replay_2128 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i156 : (formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i155 : (¬ (c0_kind ≥ (1 : Int)))) : (¬ (formula_777 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign)) := by
  exact (Or.elim (replay_2125 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i156))) (fun t1 => (False.elim (t1 (replay_2127 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i155)))))))

-- Checked replay of th-lemma.
theorem replay_2129 (c0_kind : Int) : ((c0_kind ≥ (1 : Int)) ∨ (¬ (c0_kind ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_2130 (c0_kind : Int) (i155 : (¬ (c0_kind ≥ (1 : Int)))) : (¬ (c0_kind ≥ (2 : Int))) := by
  exact (Or.elim (replay_2129 c0_kind) (fun l0 => (False.elim (i155 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2131 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i156 : (formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i155 : (¬ (c0_kind ≥ (1 : Int)))) : False := by
  exact (Or.elim (replay_2113 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) (fun l0 => (False.elim ((replay_2128 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154 i156 i155) l0))) (fun t0 => (False.elim ((replay_2130 c0_kind i155) t0))))

-- Checked replay of lemma.
theorem replay_2132 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) : ((c0_kind ≥ (1 : Int)) ∨ (¬ (formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_2131 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i154 (Classical.byContradiction (fun q => nc (Or.inr q))) (fun q => nc (Or.inl q)))

-- Checked replay of th-lemma.
theorem replay_2133 (c0_kind : Int) : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_738 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2134 (c0_kind : Int) : (((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∨ (c0_kind ≤ (0 : Int))) := by
  exact (propositional_738 (c0_kind ≤ (0 : Int)) (c0_kind ≥ (0 : Int)))

abbrev shared_expr_Repair034_28 (c0_node c2_node : Int) : Prop := (((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev shared_expr_Repair034_29 (c0_node c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev formula_791 (c0_node c2_node c2_sign : Int) : Prop := ((shared_expr_Repair034_28 c0_node c2_node) ∨ (shared_expr_Repair034_29 c0_node c2_node c2_sign))

abbrev shared_expr_Repair034_30 (c0_node c2_node : Int) : Prop := (((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))
abbrev shared_expr_Repair034_31 (c0_node c0_sign c2_node : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))))
abbrev formula_792 (c0_node c0_sign c2_node : Int) : Prop := ((shared_expr_Repair034_30 c0_node c2_node) ∨ (shared_expr_Repair034_31 c0_node c0_sign c2_node))

abbrev shared_expr_Repair034_32 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (formula_791 c0_node c2_node c2_sign)))
abbrev shared_expr_Repair034_33 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := ((shared_expr_Repair034_32 c0_depth c0_node c2_depth c2_node c2_sign) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))) ∧ (formula_792 c0_node c0_sign c2_node)))
abbrev formula_793 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_33 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_34 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair034_35 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ∨ (shared_expr_Repair034_34 c0_node c0_sign c2_node c2_sign))
abbrev formula_794 (c0_node c0_sign c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_35 c0_node c0_sign c2_node c2_sign)

abbrev shared_expr_Repair034_36 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ∧ (formula_793 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ∧ (formula_794 c0_node c0_sign c2_node c2_sign)))
abbrev formula_795 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_36 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_37 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) ∧ (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))))) ∨ ((¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int)))))))
abbrev formula_796 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_37 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

abbrev shared_expr_Repair034_38 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_797 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (shared_expr_Repair034_38 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)

abbrev shared_expr_Repair034_39 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∧ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev shared_expr_Repair034_40 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((shared_expr_Repair034_39 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ∨ ((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∧ (formula_797 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)))
abbrev formula_798 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_40 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

abbrev shared_expr_Repair034_41 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))) ∨ (¬ (formula_798 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)))
abbrev formula_799 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_41 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem propositional_739 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ p0) ∨ (¬ p1) ∨ (¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ ((¬ p2) ∨ (¬ p3) ∨ (((p4 ↔ p5) ∧ ((((¬ p6) ∨ (¬ p7)) ∧ (¬ p7)) ∨ ((¬ ((¬ p6) ∨ (¬ p7))) ∧ ((((¬ p8) ∨ (¬ p9)) ∧ (¬ p9)) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ (¬ p10)))))) ∨ ((¬ (p4 ↔ p5)) ∧ p4))))))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2135 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_799 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact (propositional_739 ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))) (c2_kind ≤ (0 : Int)) (c2_kind ≥ (0 : Int)) (c0_mode ≥ (4 : Int)) (c2_mode ≥ (4 : Int)) ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))

abbrev shared_expr_Repair034_42 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((¬ (¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))))) ∧ (((c0_level ≠ c2_level) ∧ (c0_level < c2_level)) ∨ ((¬ (c0_level ≠ c2_level)) ∧ (((c0_mode ≠ c2_mode) ∧ (c0_mode < c2_mode)) ∨ ((¬ (c0_mode ≠ c2_mode)) ∧ (c0_group < c2_group))))))
abbrev formula_800 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))) ∨ (shared_expr_Repair034_42 c0_group c0_level c0_mode c2_group c2_level c2_mode))

abbrev shared_expr_Repair034_43 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((((c2_depth + (1 : Int)) = c0_depth) ∧ (((c2_node = (c0_node / (2 : Int))) ∧ (c2_sign = (1 : Int))) ∨ ((¬ (c2_node = (c0_node / (2 : Int)))) ∧ ((c0_node / (2 : Int)) < c2_node)))) ∨ ((¬ ((c2_depth + (1 : Int)) = c0_depth)) ∧ True))
abbrev formula_801 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_43 c0_depth c0_node c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_44 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := ((((c0_depth + (1 : Int)) = c2_depth) ∧ (((c0_node = (c2_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c2_node / (2 : Int)))) ∧ (c0_node < (c2_node / (2 : Int)))))) ∨ ((¬ ((c0_depth + (1 : Int)) = c2_depth)) ∧ (formula_801 c0_depth c0_node c2_depth c2_node c2_sign)))
abbrev formula_802 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_44 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_45 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((c0_depth = c2_depth) ∧ (((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (c0_node < c2_node)))) ∨ ((¬ (c0_depth = c2_depth)) ∧ (formula_802 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
abbrev formula_803 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_45 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_46 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((c0_kind = (2 : Int)) ∧ (True ∧ (c2_kind = (1 : Int)))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ (((c2_kind = (2 : Int)) ∧ False) ∨ ((¬ (c2_kind = (2 : Int))) ∧ (formula_803 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev formula_804 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_46 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

abbrev shared_expr_Repair034_47 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ (((c2_kind = (0 : Int)) ∧ (formula_800 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ (c2_kind = (0 : Int))) ∧ True))) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (((c2_kind = (0 : Int)) ∧ False) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_804 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))))
abbrev formula_805 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_47 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

abbrev shared_expr_Repair034_48 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (((c0_level = c2_level) ∧ (((c0_mode = c2_mode) ∧ (¬ (c2_group ≤ c0_group))) ∨ ((¬ (c0_mode = c2_mode)) ∧ (¬ (c2_mode ≤ c0_mode))))) ∨ ((¬ (c0_level = c2_level)) ∧ (¬ (c2_level ≤ c0_level)))))
abbrev formula_806 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((shared_expr_Repair034_48 c0_group c0_level c0_mode c2_group c2_level c2_mode) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))

abbrev shared_expr_Repair034_49 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (c0_depth = ((-1 : Int) + c2_depth))) ∧ ((¬ (c2_depth = ((-1 : Int) + c0_depth))) ∨ (((c2_node = (c0_node / (2 : Int))) ∧ (c2_sign = (1 : Int))) ∨ ((¬ (c2_node = (c0_node / (2 : Int)))) ∧ (¬ (c2_node ≤ (c0_node / (2 : Int))))))))
abbrev shared_expr_Repair034_50 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((c0_depth = ((-1 : Int) + c2_depth)) ∧ (((c0_node = (c2_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c2_node / (2 : Int)))) ∧ (¬ ((c2_node / (2 : Int)) ≤ c0_node))))) ∨ (shared_expr_Repair034_49 c0_depth c0_node c2_depth c2_node c2_sign))
abbrev formula_807 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_50 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_51 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((c0_depth = c2_depth) ∧ (((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (¬ (c2_node ≤ c0_node))))) ∨ ((¬ (c0_depth = c2_depth)) ∧ (formula_807 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
abbrev formula_808 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_51 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_52 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (c2_kind = (0 : Int))) ∧ (((c0_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_808 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev formula_809 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_52 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

abbrev shared_expr_Repair034_53 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ ((¬ (c2_kind = (0 : Int))) ∨ (formula_806 c0_group c0_level c0_mode c2_group c2_level c2_mode))) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (formula_809 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
abbrev formula_810 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_53 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

abbrev shared_expr_Repair034_54 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_810 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_811 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_54 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_740 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 : Prop) : (((p0 ∧ ((p1 ∧ (((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2)) ∨ ((¬ (¬ ((¬ p2) ↔ (¬ p3)))) ∧ (((¬ p4) ∧ p5) ∨ ((¬ (¬ p4)) ∧ (((¬ p6) ∧ p7) ∨ ((¬ (¬ p6)) ∧ p8))))))) ∨ ((¬ p1) ∧ True))) ∨ ((¬ p0) ∧ ((p1 ∧ False) ∨ ((¬ p1) ∧ ((p9 ∧ (True ∧ p10)) ∨ ((¬ p9) ∧ ((p11 ∧ False) ∨ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ p15))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((p18 ∧ ((p19 ∧ p20) ∨ ((¬ p19) ∧ p21))) ∨ ((¬ p18) ∧ True)))))))))))))) ↔ ((p0 ∧ ((¬ p1) ∨ ((((¬ p2) ↔ (¬ p3)) ∧ ((p4 ∧ ((p6 ∧ (¬ (¬ p8))) ∨ ((¬ p6) ∧ (¬ (¬ p7))))) ∨ ((¬ p4) ∧ (¬ (¬ p5))))) ∨ ((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2))))) ∨ ((¬ p0) ∧ ((¬ p1) ∧ ((p9 ∧ p10) ∨ ((¬ p9) ∧ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ (¬ (¬ p15))))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((¬ p18) ∨ ((p19 ∧ p20) ∨ ((¬ p19) ∧ (¬ (¬ p21)))))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2946 (c0_mode c2_mode : Int) : (¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ↔ (¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) := (not_congr (iff_congr (normalization_693 c0_mode) (normalization_1211 c2_mode)))

theorem normalization_2947 (c0_level c2_level : Int) : (c0_level ≠ c2_level) ↔ (¬ (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_2948 (c0_level c2_level : Int) : (c0_level < c2_level) ↔ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2949 (c0_mode c2_mode : Int) : (c0_mode ≠ c2_mode) ↔ (¬ (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_2950 (c0_mode c2_mode : Int) : (c0_mode < c2_mode) ↔ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2951 (c0_group c2_group : Int) : (c0_group < c2_group) ↔ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair034_55 (c0_group c0_mode c2_group c2_mode : Int) : Prop := (((¬ (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))))) ∧ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))
theorem normalization_2952 (c0_group c0_mode c2_group c2_mode : Int) : (((c0_mode ≠ c2_mode) ∧ (c0_mode < c2_mode)) ∨ ((¬ (c0_mode ≠ c2_mode)) ∧ (c0_group < c2_group))) ↔ (shared_expr_Repair034_55 c0_group c0_mode c2_group c2_mode) := (or_congr (and_congr (normalization_2949 c0_mode c2_mode) (normalization_2950 c0_mode c2_mode)) (and_congr (not_congr (normalization_2949 c0_mode c2_mode)) (normalization_2951 c0_group c2_group)))

abbrev shared_expr_Repair034_56 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((¬ (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair034_55 c0_group c0_mode c2_group c2_mode)))
theorem normalization_2953 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (((c0_level ≠ c2_level) ∧ (c0_level < c2_level)) ∨ ((¬ (c0_level ≠ c2_level)) ∧ (((c0_mode ≠ c2_mode) ∧ (c0_mode < c2_mode)) ∨ ((¬ (c0_mode ≠ c2_mode)) ∧ (c0_group < c2_group))))) ↔ (shared_expr_Repair034_56 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_2947 c0_level c2_level) (normalization_2948 c0_level c2_level)) (and_congr (not_congr (normalization_2947 c0_level c2_level)) (normalization_2952 c0_group c0_mode c2_group c2_mode)))

abbrev shared_expr_Repair034_57 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))) ∨ ((¬ (¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair034_56 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
theorem normalization_2954 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_800 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair034_57 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_2946 c0_mode c2_mode) (normalization_693 c0_mode)) (and_congr (not_congr (normalization_2946 c0_mode c2_mode)) (normalization_2953 c0_group c0_level c0_mode c2_group c2_level c2_mode)))

abbrev shared_expr_Repair034_58 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair034_57 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ True))
theorem normalization_2955 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : (((c2_kind = (0 : Int)) ∧ (formula_800 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ (c2_kind = (0 : Int))) ∧ True)) ↔ (shared_expr_Repair034_58 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := (or_congr (and_congr (normalization_0 c2_kind) (normalization_2954 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (and_congr (not_congr (normalization_0 c2_kind)) (normalization_305)))

theorem normalization_2956 (c2_kind : Int) : (True ∧ (c2_kind = (1 : Int))) ↔ (True ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) := (and_congr (normalization_305) (normalization_16 c2_kind))

theorem normalization_2957 (c0_depth c2_depth : Int) : (c0_depth = c2_depth) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2958 (c0_node c2_node : Int) : (c0_node = c2_node) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2959 (c0_sign c2_sign : Int) : ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) := (and_congr (normalization_144 c0_sign) (normalization_26 c2_sign))

theorem normalization_2960 (c0_node c2_node : Int) : (c0_node < c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair034_59 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair034_60 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair034_59 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))
theorem normalization_2961 (c0_node c0_sign c2_node c2_sign : Int) : (((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (c0_node < c2_node))) ↔ (shared_expr_Repair034_60 c0_node c0_sign c2_node c2_sign) := (or_congr (and_congr (normalization_2958 c0_node c2_node) (normalization_2959 c0_sign c2_sign)) (and_congr (not_congr (normalization_2958 c0_node c2_node)) (normalization_2960 c0_node c2_node)))

theorem normalization_2962 (c0_depth c2_depth : Int) : ((c0_depth + (1 : Int)) = c2_depth) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_2963 (c0_node c2_node : Int) : (c0_node = (c2_node / (2 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2964 (c0_node c2_node : Int) : (c0_node < (c2_node / (2 : Int))) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

abbrev shared_expr_Repair034_61 (c0_node c2_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair034_62 (c0_node c0_sign c2_node : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair034_61 c0_node c2_node))
theorem normalization_2965 (c0_node c0_sign c2_node : Int) : (((c0_node = (c2_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c2_node / (2 : Int)))) ∧ (c0_node < (c2_node / (2 : Int))))) ↔ (shared_expr_Repair034_62 c0_node c0_sign c2_node) := (or_congr (and_congr (normalization_2963 c0_node c2_node) (normalization_144 c0_sign)) (and_congr (not_congr (normalization_2963 c0_node c2_node)) (normalization_2964 c0_node c2_node)))

theorem normalization_2966 (c0_depth c2_depth : Int) : ((c2_depth + (1 : Int)) = c0_depth) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_2967 (c0_node c2_node : Int) : (c2_node = (c0_node / (2 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2968 (c0_node c2_node : Int) : ((c0_node / (2 : Int)) < c2_node) ↔ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair034_63 (c0_node c2_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
abbrev shared_expr_Repair034_64 (c0_node c2_node c2_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair034_63 c0_node c2_node))
theorem normalization_2969 (c0_node c2_node c2_sign : Int) : (((c2_node = (c0_node / (2 : Int))) ∧ (c2_sign = (1 : Int))) ∨ ((¬ (c2_node = (c0_node / (2 : Int)))) ∧ ((c0_node / (2 : Int)) < c2_node))) ↔ (shared_expr_Repair034_64 c0_node c2_node c2_sign) := (or_congr (and_congr (normalization_2967 c0_node c2_node) (normalization_26 c2_sign)) (and_congr (not_congr (normalization_2967 c0_node c2_node)) (normalization_2968 c0_node c2_node)))

abbrev shared_expr_Repair034_65 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∧ (shared_expr_Repair034_64 c0_node c2_node c2_sign)) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)))) ∧ True))
theorem normalization_2970 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : (formula_801 c0_depth c0_node c2_depth c2_node c2_sign) ↔ (shared_expr_Repair034_65 c0_depth c0_node c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_2966 c0_depth c2_depth) (normalization_2969 c0_node c2_node c2_sign)) (and_congr (not_congr (normalization_2966 c0_depth c2_depth)) (normalization_305)))

abbrev shared_expr_Repair034_66 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair034_62 c0_node c0_sign c2_node)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair034_65 c0_depth c0_node c2_depth c2_node c2_sign)))
theorem normalization_2971 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_802 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair034_66 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_2962 c0_depth c2_depth) (normalization_2965 c0_node c0_sign c2_node)) (and_congr (not_congr (normalization_2962 c0_depth c2_depth)) (normalization_2970 c0_depth c0_node c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair034_67 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair034_60 c0_node c0_sign c2_node c2_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_66 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
theorem normalization_2972 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_803 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair034_67 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_2957 c0_depth c2_depth) (normalization_2961 c0_node c0_sign c2_node c2_sign)) (and_congr (not_congr (normalization_2957 c0_depth c2_depth)) (normalization_2971 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair034_68 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ False) ∨ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair034_67 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
theorem normalization_2973 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (((c2_kind = (2 : Int)) ∧ False) ∨ ((¬ (c2_kind = (2 : Int))) ∧ (formula_803 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))) ↔ (shared_expr_Repair034_68 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_34 c2_kind) (normalization_1253)) (and_congr (not_congr (normalization_34 c2_kind)) (normalization_2972 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair034_69 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (True ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))))) ∨ ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair034_68 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_2974 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_804 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ (shared_expr_Repair034_69 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_141 c0_kind) (normalization_2956 c2_kind)) (and_congr (not_congr (normalization_141 c0_kind)) (normalization_2973 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair034_70 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ False) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_69 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_2975 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (((c2_kind = (0 : Int)) ∧ False) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_804 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))) ↔ (shared_expr_Repair034_70 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_0 c2_kind) (normalization_1253)) (and_congr (not_congr (normalization_0 c2_kind)) (normalization_2974 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair034_71 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair034_58 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_70 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_2976 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair034_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (or_congr (and_congr (normalization_134 c0_kind) (normalization_2955 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) (and_congr (not_congr (normalization_134 c0_kind)) (normalization_2975 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

theorem normalization_2977 (c2_kind : Int) : (¬ (c2_kind = (0 : Int))) ↔ (¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) := (not_congr (normalization_0 c2_kind))

theorem normalization_2978 (c0_mode c2_mode : Int) : ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ↔ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) := (iff_congr (normalization_693 c0_mode) (normalization_1211 c2_mode))

theorem normalization_2979 (c0_level c2_level : Int) : (c0_level = c2_level) ↔ (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2980 (c0_mode c2_mode : Int) : (c0_mode = c2_mode) ↔ (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2981 (c0_group c2_group : Int) : (c2_group ≤ c0_group) ↔ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2982 (c0_group c2_group : Int) : (¬ (c2_group ≤ c0_group)) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int)))) := (not_congr (normalization_2981 c0_group c2_group))

theorem normalization_2983 (c0_mode c2_mode : Int) : (c2_mode ≤ c0_mode) ↔ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2984 (c0_mode c2_mode : Int) : (¬ (c2_mode ≤ c0_mode)) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_2983 c0_mode c2_mode))

abbrev shared_expr_Repair034_72 (c0_group c0_mode c2_group c2_mode : Int) : Prop := (((((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))))
theorem normalization_2985 (c0_group c0_mode c2_group c2_mode : Int) : (((c0_mode = c2_mode) ∧ (¬ (c2_group ≤ c0_group))) ∨ ((¬ (c0_mode = c2_mode)) ∧ (¬ (c2_mode ≤ c0_mode)))) ↔ (shared_expr_Repair034_72 c0_group c0_mode c2_group c2_mode) := (or_congr (and_congr (normalization_2980 c0_mode c2_mode) (normalization_2982 c0_group c2_group)) (and_congr (not_congr (normalization_2980 c0_mode c2_mode)) (normalization_2984 c0_mode c2_mode)))

theorem normalization_2986 (c0_level c2_level : Int) : (c2_level ≤ c0_level) ↔ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2987 (c0_level c2_level : Int) : (¬ (c2_level ≤ c0_level)) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_2986 c0_level c2_level))

abbrev shared_expr_Repair034_73 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair034_72 c0_group c0_mode c2_group c2_mode)) ∨ ((¬ (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))))
theorem normalization_2988 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (((c0_level = c2_level) ∧ (((c0_mode = c2_mode) ∧ (¬ (c2_group ≤ c0_group))) ∨ ((¬ (c0_mode = c2_mode)) ∧ (¬ (c2_mode ≤ c0_mode))))) ∨ ((¬ (c0_level = c2_level)) ∧ (¬ (c2_level ≤ c0_level)))) ↔ (shared_expr_Repair034_73 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_2979 c0_level c2_level) (normalization_2985 c0_group c0_mode c2_group c2_mode)) (and_congr (not_congr (normalization_2979 c0_level c2_level)) (normalization_2987 c0_level c2_level)))

abbrev shared_expr_Repair034_74 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair034_73 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_2989 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_806 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair034_74 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_2978 c0_mode c2_mode) (normalization_2988 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (and_congr (not_congr (normalization_2978 c0_mode c2_mode)) (normalization_693 c0_mode)))

theorem normalization_2990 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((¬ (c2_kind = (0 : Int))) ∨ (formula_806 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ↔ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair034_74 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := (or_congr (normalization_2977 c2_kind) (normalization_2989 c0_group c0_level c0_mode c2_group c2_level c2_mode))

theorem normalization_2991 (c2_kind : Int) : (¬ (c2_kind = (2 : Int))) ↔ (¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) := (not_congr (normalization_34 c2_kind))

theorem normalization_2992 (c0_node c2_node : Int) : (c2_node ≤ c0_node) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2993 (c0_node c2_node : Int) : (¬ (c2_node ≤ c0_node)) ↔ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2992 c0_node c2_node))

abbrev shared_expr_Repair034_75 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair034_59 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
theorem normalization_2994 (c0_node c0_sign c2_node c2_sign : Int) : (((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (¬ (c2_node ≤ c0_node)))) ↔ (shared_expr_Repair034_75 c0_node c0_sign c2_node c2_sign) := (or_congr (and_congr (normalization_2958 c0_node c2_node) (normalization_2959 c0_sign c2_sign)) (and_congr (not_congr (normalization_2958 c0_node c2_node)) (normalization_2993 c0_node c2_node)))

theorem normalization_2995 (c0_depth c2_depth : Int) : (c0_depth = ((-1 : Int) + c2_depth)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_2996 (c0_node c2_node : Int) : ((c2_node / (2 : Int)) ≤ c0_node) ↔ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2997 (c0_node c2_node : Int) : (¬ ((c2_node / (2 : Int)) ≤ c0_node)) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (not_congr (normalization_2996 c0_node c2_node))

theorem normalization_2998 (c0_node c0_sign c2_node : Int) : (((c0_node = (c2_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c2_node / (2 : Int)))) ∧ (¬ ((c2_node / (2 : Int)) ≤ c0_node)))) ↔ (shared_expr_Repair034_62 c0_node c0_sign c2_node) := (or_congr (and_congr (normalization_2963 c0_node c2_node) (normalization_144 c0_sign)) (and_congr (not_congr (normalization_2963 c0_node c2_node)) (normalization_2997 c0_node c2_node)))

theorem normalization_2999 (c0_depth c2_depth : Int) : (c2_depth = ((-1 : Int) + c0_depth)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_3000 (c0_depth c2_depth : Int) : (¬ (c2_depth = ((-1 : Int) + c0_depth))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)))) := (not_congr (normalization_2999 c0_depth c2_depth))

theorem normalization_3001 (c0_node c2_node : Int) : (c2_node ≤ (c0_node / (2 : Int))) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3002 (c0_node c2_node : Int) : (¬ (c2_node ≤ (c0_node / (2 : Int)))) ↔ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_3001 c0_node c2_node))

abbrev shared_expr_Repair034_76 (c0_node c2_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair034_77 (c0_node c2_node c2_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair034_76 c0_node c2_node))
theorem normalization_3003 (c0_node c2_node c2_sign : Int) : (((c2_node = (c0_node / (2 : Int))) ∧ (c2_sign = (1 : Int))) ∨ ((¬ (c2_node = (c0_node / (2 : Int)))) ∧ (¬ (c2_node ≤ (c0_node / (2 : Int)))))) ↔ (shared_expr_Repair034_77 c0_node c2_node c2_sign) := (or_congr (and_congr (normalization_2967 c0_node c2_node) (normalization_26 c2_sign)) (and_congr (not_congr (normalization_2967 c0_node c2_node)) (normalization_3002 c0_node c2_node)))

theorem normalization_3004 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : ((¬ (c2_depth = ((-1 : Int) + c0_depth))) ∨ (((c2_node = (c0_node / (2 : Int))) ∧ (c2_sign = (1 : Int))) ∨ ((¬ (c2_node = (c0_node / (2 : Int)))) ∧ (¬ (c2_node ≤ (c0_node / (2 : Int))))))) ↔ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair034_77 c0_node c2_node c2_sign)) := (or_congr (normalization_3000 c0_depth c2_depth) (normalization_3003 c0_node c2_node c2_sign))

abbrev shared_expr_Repair034_78 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair034_77 c0_node c2_node c2_sign)))
abbrev shared_expr_Repair034_79 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair034_62 c0_node c0_sign c2_node)) ∨ (shared_expr_Repair034_78 c0_depth c0_node c2_depth c2_node c2_sign))
theorem normalization_3005 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_807 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair034_79 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_2995 c0_depth c2_depth) (normalization_2998 c0_node c0_sign c2_node)) (and_congr (not_congr (normalization_2995 c0_depth c2_depth)) (normalization_3004 c0_depth c0_node c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair034_80 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair034_75 c0_node c0_sign c2_node c2_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_79 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
theorem normalization_3006 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_808 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair034_80 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_2957 c0_depth c2_depth) (normalization_2994 c0_node c0_sign c2_node c2_sign)) (and_congr (not_congr (normalization_2957 c0_depth c2_depth)) (normalization_3005 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))

theorem normalization_3007 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : ((¬ (c2_kind = (2 : Int))) ∧ (formula_808 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair034_80 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := (and_congr (normalization_2991 c2_kind) (normalization_3006 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

abbrev shared_expr_Repair034_81 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair034_80 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
abbrev shared_expr_Repair034_82 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair034_81 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
theorem normalization_3008 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (((c0_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_808 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))) ↔ (shared_expr_Repair034_82 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_141 c0_kind) (normalization_16 c2_kind)) (and_congr (not_congr (normalization_141 c0_kind)) (normalization_3007 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

theorem normalization_3009 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_809 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_82 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (and_congr (normalization_2977 c2_kind) (normalization_3008 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair034_83 (c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair034_74 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
abbrev shared_expr_Repair034_84 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_82 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_3010 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_810 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ ((shared_expr_Repair034_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair034_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (or_congr (and_congr (normalization_134 c0_kind) (normalization_2990 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) (and_congr (not_congr (normalization_134 c0_kind)) (normalization_3009 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair034_85 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((shared_expr_Repair034_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ ((shared_expr_Repair034_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair034_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_3011 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_811 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair034_85 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_2976 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_3010 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2136 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_811 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_740 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((c0_mode) ≤ (3 : Int)) ((c2_mode) ≤ (3 : Int)) (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int)) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) (shared_expr_Repair034_62 c0_node c0_sign c2_node) ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3011 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

-- Checked replay of mp.
theorem replay_2137 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_810 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact Iff.mp (replay_2136 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) i157

abbrev shared_expr_Repair034_86 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_810 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_810 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_812 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_86 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_741 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair034_87 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair034_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair034_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair034_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair034_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_3012 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_812 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair034_87 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_3010 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_3010 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2138 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_812 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_741 ((shared_expr_Repair034_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair034_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
  have hn := ht
  exact Iff.mpr (normalization_3012 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

-- Checked replay of mp.
theorem replay_2139 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_810 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact Iff.mp (replay_2138 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2137 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157)

abbrev shared_expr_Repair034_88 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((c0_level = c2_level) ∧ (((c0_mode = c2_mode) ∧ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ∨ ((¬ (c0_mode = c2_mode)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))))) ∨ ((¬ (c0_level = c2_level)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))))
abbrev formula_813 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (shared_expr_Repair034_88 c0_group c0_level c0_mode c2_group c2_level c2_mode)

abbrev shared_expr_Repair034_89 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((¬ (c2_kind = (0 : Int))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_813 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_814 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (shared_expr_Repair034_89 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)

abbrev shared_expr_Repair034_90 (c0_node c0_sign c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ∧ (c0_sign = (0 : Int))) ∨ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))))
abbrev formula_815 (c0_node c0_sign c2_node : Int) : Prop := (shared_expr_Repair034_90 c0_node c0_sign c2_node)

abbrev shared_expr_Repair034_91 (c0_node c2_node c2_sign : Int) : Prop := ((((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ∧ (c2_sign = (1 : Int))) ∨ ((¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_816 (c0_node c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_91 c0_node c2_node c2_sign)

abbrev shared_expr_Repair034_92 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ∧ (formula_815 c0_node c0_sign c2_node)) ∨ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ∨ (formula_816 c0_node c2_node c2_sign))))
abbrev formula_817 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_92 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_93 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((c0_depth = c2_depth) ∧ (((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ∨ ((¬ (c0_depth = c2_depth)) ∧ (formula_817 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
abbrev formula_818 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_93 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)

abbrev shared_expr_Repair034_94 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (c2_kind = (0 : Int))) ∧ (((c0_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev formula_819 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_94 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

abbrev shared_expr_Repair034_95 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ (formula_814 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (formula_819 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
abbrev formula_820 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_95 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

abbrev shared_expr_Repair034_96 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := ((formula_810 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (formula_820 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))
abbrev formula_821 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (shared_expr_Repair034_96 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)

theorem normalized_742 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ ((¬ p10) ∧ p11)) ∨ p12))))))))))) ↔ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ (p11 ∧ (¬ p10))) ∨ p12)))))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3013 (c0_group c2_group : Int) : ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)) ↔ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3014 (c0_group c2_group : Int) : (¬ ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int)))) := (not_congr (normalization_3013 c0_group c2_group))

theorem normalization_3015 (c0_mode c2_mode : Int) : ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ↔ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3016 (c0_mode c2_mode : Int) : (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_3015 c0_mode c2_mode))

theorem normalization_3017 (c0_group c0_mode c2_group c2_mode : Int) : (((c0_mode = c2_mode) ∧ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))) ∨ ((¬ (c0_mode = c2_mode)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ↔ (shared_expr_Repair034_72 c0_group c0_mode c2_group c2_mode) := (or_congr (and_congr (normalization_2980 c0_mode c2_mode) (normalization_3014 c0_group c2_group)) (and_congr (not_congr (normalization_2980 c0_mode c2_mode)) (normalization_3016 c0_mode c2_mode)))

theorem normalization_3018 (c0_level c2_level : Int) : ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ↔ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3019 (c0_level c2_level : Int) : (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_3018 c0_level c2_level))

theorem normalization_3020 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_813 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair034_73 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_2979 c0_level c2_level) (normalization_3017 c0_group c0_mode c2_group c2_mode)) (and_congr (not_congr (normalization_2979 c0_level c2_level)) (normalization_3019 c0_level c2_level)))

theorem normalization_3021 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_813 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))) ↔ (shared_expr_Repair034_74 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_2978 c0_mode c2_mode) (normalization_3020 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (and_congr (not_congr (normalization_2978 c0_mode c2_mode)) (normalization_693 c0_mode)))

theorem normalization_3022 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : (formula_814 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair034_74 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := (or_congr (normalization_2977 c2_kind) (normalization_3021 c0_group c0_level c0_mode c2_group c2_level c2_mode))

theorem normalization_3023 (c0_node c2_node : Int) : ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3024 (c0_node c2_node : Int) : (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_3023 c0_node c2_node))

theorem normalization_3025 (c0_node c0_sign c2_node c2_sign : Int) : (((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (shared_expr_Repair034_75 c0_node c0_sign c2_node c2_sign) := (or_congr (and_congr (normalization_2958 c0_node c2_node) (normalization_2959 c0_sign c2_sign)) (and_congr (not_congr (normalization_2958 c0_node c2_node)) (normalization_3024 c0_node c2_node)))

theorem normalization_3026 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_3027 (c0_node c2_node : Int) : ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_3028 (c0_node c2_node : Int) : ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3029 (c0_node c2_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (not_congr (normalization_3028 c0_node c2_node))

theorem normalization_3030 (c0_node c0_sign c2_node : Int) : (formula_815 c0_node c0_sign c2_node) ↔ (shared_expr_Repair034_62 c0_node c0_sign c2_node) := (or_congr (and_congr (normalization_3027 c0_node c2_node) (normalization_144 c0_sign)) (and_congr (not_congr (normalization_3027 c0_node c2_node)) (normalization_3029 c0_node c2_node)))

theorem normalization_3031 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := by
  omega

theorem normalization_3032 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ (¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) := (not_congr (normalization_3031 c0_depth c2_depth))

theorem normalization_3033 (c0_node c2_node : Int) : ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_3034 (c0_node c2_node : Int) : ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3035 (c0_node c2_node : Int) : (¬ ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_3034 c0_node c2_node))

theorem normalization_3036 (c0_node c2_node c2_sign : Int) : (formula_816 c0_node c2_node c2_sign) ↔ (shared_expr_Repair034_77 c0_node c2_node c2_sign) := (or_congr (and_congr (normalization_3033 c0_node c2_node) (normalization_26 c2_sign)) (and_congr (not_congr (normalization_3033 c0_node c2_node)) (normalization_3035 c0_node c2_node)))

theorem normalization_3037 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ∨ (formula_816 c0_node c2_node c2_sign)) ↔ ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair034_77 c0_node c2_node c2_sign)) := (or_congr (normalization_3032 c0_depth c2_depth) (normalization_3036 c0_node c2_node c2_sign))

abbrev shared_expr_Repair034_97 (c0_depth c0_node c2_depth c2_node c2_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair034_77 c0_node c2_node c2_sign)))
abbrev shared_expr_Repair034_98 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair034_62 c0_node c0_sign c2_node)) ∨ (shared_expr_Repair034_97 c0_depth c0_node c2_depth c2_node c2_sign))
theorem normalization_3038 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_817 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair034_98 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_3026 c0_depth c2_depth) (normalization_3030 c0_node c0_sign c2_node)) (and_congr (not_congr (normalization_3026 c0_depth c2_depth)) (normalization_3037 c0_depth c0_node c2_depth c2_node c2_sign)))

abbrev shared_expr_Repair034_99 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair034_75 c0_node c0_sign c2_node c2_sign)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_98 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
theorem normalization_3039 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign : Int) : (formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) ↔ (shared_expr_Repair034_99 c0_depth c0_node c0_sign c2_depth c2_node c2_sign) := (or_congr (and_congr (normalization_2957 c0_depth c2_depth) (normalization_3025 c0_node c0_sign c2_node c2_sign)) (and_congr (not_congr (normalization_2957 c0_depth c2_depth)) (normalization_3038 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))

theorem normalization_3040 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : ((¬ (c2_kind = (2 : Int))) ∧ (formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) ↔ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair034_99 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)) := (and_congr (normalization_2991 c2_kind) (normalization_3039 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))

abbrev shared_expr_Repair034_100 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair034_99 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))
abbrev shared_expr_Repair034_101 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair034_100 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
theorem normalization_3041 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (((c0_kind = (2 : Int)) ∧ (c2_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c2_kind = (2 : Int))) ∧ (formula_818 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))) ↔ (shared_expr_Repair034_101 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := (or_congr (and_congr (normalization_141 c0_kind) (normalization_16 c2_kind)) (and_congr (not_congr (normalization_141 c0_kind)) (normalization_3040 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

theorem normalization_3042 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_819 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) ↔ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_101 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (and_congr (normalization_2977 c2_kind) (normalization_3041 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

abbrev shared_expr_Repair034_102 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair034_101 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_3043 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_820 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ ((shared_expr_Repair034_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair034_102 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) := (or_congr (and_congr (normalization_134 c0_kind) (normalization_3022 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) (and_congr (not_congr (normalization_134 c0_kind)) (normalization_3042 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))

abbrev shared_expr_Repair034_103 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : Prop := (((shared_expr_Repair034_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair034_84 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ↔ ((shared_expr_Repair034_83 c0_group c0_kind c0_level c0_mode c2_group c2_kind c2_level c2_mode) ∨ (shared_expr_Repair034_102 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))
theorem normalization_3044 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_821 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) ↔ (shared_expr_Repair034_103 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := (iff_congr (normalization_3010 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (normalization_3043 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2140 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) : (formula_821 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  classical
  have ht := (normalized_742 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair034_74 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (shared_expr_Repair034_75 c0_node c0_sign c2_node c2_sign) (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) (shared_expr_Repair034_62 c0_node c0_sign c2_node) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) (shared_expr_Repair034_77 c0_node c2_node c2_sign))
  have hn := ht
  exact Iff.mpr (normalization_3044 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) hn

-- Checked replay of mp.
theorem replay_2141 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) : (formula_820 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) := by
  exact Iff.mp (replay_2140 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign) (replay_2139 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157)

theorem normalized_743 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3045 (c2_kind : Int) : (¬ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) := (not_congr (normalization_1003 c2_kind))

theorem normalization_3046 (c2_kind : Int) : ((¬ (c2_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))))) ↔ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))))) := (iff_congr (normalization_2977 c2_kind) (normalization_3045 c2_kind))

-- Checked replay of monotonicity.
theorem replay_2142 (c2_kind : Int) : ((¬ (c2_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_743 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))
  have n0 : ((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1005 c2_kind) (replay_172 c2_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_3046 c2_kind) hn

theorem normalized_744 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3047 (c2_kind : Int) : ((¬ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) ↔ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ↔ ((¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_3045 c2_kind) (normalization_1002 c2_kind))

-- Checked replay of rewrite.
theorem replay_2143 (c2_kind : Int) : ((¬ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))))) ↔ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_744 ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_3047 c2_kind) hn

end H4Formal.Generated.Repair
