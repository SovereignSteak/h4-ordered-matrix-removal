import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification077

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_1783 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_0 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∧ ((¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
abbrev shared_expr_Classification078_1 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_6809 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group))) ↔ (¬ (formula_2034 c3_group c3_level c3_mode r1_group r1_level r1_mode))) ↔ ((shared_expr_Classification078_0 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Classification078_1 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := (iff_congr (normalization_6630 c3_group c3_level c3_mode r1_group r1_level r1_mode) (normalization_6807 c3_group c3_level c3_mode r1_group r1_level r1_mode))

-- Checked replay of trans.
abbrev shared_expr_Classification078_2 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem replay_4950 (c3_group c3_level c3_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c3_mode) ∧ (r1_level = c3_level) ∧ (¬ (r1_group = c3_group))) ↔ (¬ (formula_2034 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := by
  classical
  have ht := (normalized_1783 (shared_expr_Classification078_0 c3_group c3_level c3_mode r1_group r1_level r1_mode) (shared_expr_Classification078_2 c3_group c3_level c3_mode r1_group r1_level r1_mode) (shared_expr_Classification078_1 c3_group c3_level c3_mode r1_group r1_level r1_mode))
  have n0 : ((shared_expr_Classification078_0 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_2 c3_group c3_level c3_mode r1_group r1_level r1_mode)) := by
    exact Iff.mp (normalization_6805 c3_group c3_level c3_mode r1_group r1_level r1_mode) (replay_4948 c3_group c3_level c3_mode r1_group r1_level r1_mode)
  have n1 : ((shared_expr_Classification078_2 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Classification078_1 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := by
    exact Iff.mp (normalization_6808 c3_group c3_level c3_mode r1_group r1_level r1_mode) (replay_4949 c3_group c3_level c3_mode r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6809 c3_group c3_level c3_mode r1_group r1_level r1_mode) hn

-- Checked replay of rewrite.
theorem replay_4951 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((formula_2113 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (formula_2033 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) := by
  classical
  first
  | (simp only [formula_2113, shared_expr_Classification077_85, formula_2107, shared_expr_Classification077_79, formula_2108, shared_expr_Classification077_80, formula_2109, shared_expr_Classification077_81, formula_2110, shared_expr_Classification077_82, formula_2111, shared_expr_Classification077_83, formula_2112, shared_expr_Classification077_84, formula_2033, shared_expr_Classification076_16, formula_2022, shared_expr_Classification076_5, formula_2021, shared_expr_Classification076_4, formula_2024, shared_expr_Classification076_7, formula_2023, shared_expr_Classification076_6, formula_2026, shared_expr_Classification076_9, formula_2025, shared_expr_Classification076_8, formula_2028, shared_expr_Classification076_11, formula_2027, shared_expr_Classification076_10, formula_2030, shared_expr_Classification076_13, formula_2029, shared_expr_Classification076_12, formula_2032, shared_expr_Classification076_15, formula_2031, shared_expr_Classification076_14, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Classification078_3 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∧ (¬ (formula_2034 c3_group c3_level c3_mode r1_group r1_level r1_mode))) ∨ ((¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ∧ (formula_2033 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
abbrev formula_2129 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification078_3 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)

abbrev shared_expr_Classification078_4 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((formula_2114 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (formula_2129 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))
abbrev formula_2130 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification078_4 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)

theorem normalized_1784 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6810 (c3_kind : Int) : (c3_kind ≤ (1 : Int)) ↔ ((c3_kind) ≤ (1 : Int)) := by
  omega

theorem normalization_6811 (c3_kind : Int) : (¬ (c3_kind ≤ (1 : Int))) ↔ (¬ ((c3_kind) ≤ (1 : Int))) := (not_congr (normalization_6810 c3_kind))

theorem normalization_6812 (c3_kind : Int) : (c3_kind ≥ (1 : Int)) ↔ (¬ ((c3_kind) ≤ (0 : Int))) := by
  omega

theorem normalization_6813 (c3_kind : Int) : (¬ (c3_kind ≥ (1 : Int))) ↔ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) := (not_congr (normalization_6812 c3_kind))

theorem normalization_6814 (c3_sign : Int) : (c3_sign ≤ (0 : Int)) ↔ ((c3_sign) ≤ (0 : Int)) := by
  omega

theorem normalization_6815 (c3_sign : Int) : (¬ (c3_sign ≤ (0 : Int))) ↔ (¬ ((c3_sign) ≤ (0 : Int))) := (not_congr (normalization_6814 c3_sign))

theorem normalization_6816 (c3_sign : Int) : (c3_sign ≥ (0 : Int)) ↔ (¬ ((c3_sign) ≤ (-1 : Int))) := by
  omega

theorem normalization_6817 (c3_sign : Int) : (¬ (c3_sign ≥ (0 : Int))) ↔ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) := (not_congr (normalization_6816 c3_sign))

theorem normalization_6818 (c3_sign : Int) : ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))) ↔ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))) := (or_congr (normalization_6815 c3_sign) (normalization_6817 c3_sign))

theorem normalization_6819 (c3_sign : Int) : (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ↔ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) := (not_congr (normalization_6818 c3_sign))

theorem normalization_6820 (c3_sign : Int) : (c3_sign ≤ (2 : Int)) ↔ ((c3_sign) ≤ (2 : Int)) := by
  omega

theorem normalization_6821 (c3_sign : Int) : (¬ (c3_sign ≤ (2 : Int))) ↔ (¬ ((c3_sign) ≤ (2 : Int))) := (not_congr (normalization_6820 c3_sign))

theorem normalization_6822 (c3_sign : Int) : (c3_sign ≥ (2 : Int)) ↔ (¬ ((c3_sign) ≤ (1 : Int))) := by
  omega

theorem normalization_6823 (c3_sign : Int) : (¬ (c3_sign ≥ (2 : Int))) ↔ (¬ (¬ ((c3_sign) ≤ (1 : Int)))) := (not_congr (normalization_6822 c3_sign))

theorem normalization_6824 (c3_sign : Int) : ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))) ↔ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))) := (or_congr (normalization_6821 c3_sign) (normalization_6823 c3_sign))

theorem normalization_6825 (c3_sign : Int) : (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))) ↔ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))) := (not_congr (normalization_6824 c3_sign))

theorem normalization_6826 (c3_sign : Int) : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) := (or_congr (normalization_6819 c3_sign) (normalization_6825 c3_sign))

theorem normalization_6827 (c3_sign : Int) : (¬ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_6826 c3_sign))

theorem normalization_6828 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_6829 (c3_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) := (not_congr (normalization_6828 c3_depth r1_level))

theorem normalization_6830 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_6831 (c3_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := (not_congr (normalization_6830 c3_depth r1_level))

abbrev shared_expr_Classification078_5 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_6832 (c3_depth c3_kind c3_sign r1_level : Int) : (formula_2021 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Classification078_5 c3_depth c3_kind c3_sign r1_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6827 c3_sign) (or_congr (normalization_6829 c3_depth r1_level) (normalization_6831 c3_depth r1_level)))))

theorem normalization_6833 (c3_depth c3_kind c3_sign r1_level : Int) : (¬ (formula_2021 c3_depth c3_kind c3_sign r1_level)) ↔ (¬ (shared_expr_Classification078_5 c3_depth c3_kind c3_sign r1_level)) := (not_congr (normalization_6832 c3_depth c3_kind c3_sign r1_level))

theorem normalization_6834 (c3_kind : Int) : (c3_kind ≤ (2 : Int)) ↔ ((c3_kind) ≤ (2 : Int)) := by
  omega

theorem normalization_6835 (c3_kind : Int) : (¬ (c3_kind ≤ (2 : Int))) ↔ (¬ ((c3_kind) ≤ (2 : Int))) := (not_congr (normalization_6834 c3_kind))

theorem normalization_6836 (c3_kind : Int) : (c3_kind ≥ (2 : Int)) ↔ (¬ ((c3_kind) ≤ (1 : Int))) := by
  omega

theorem normalization_6837 (c3_kind : Int) : (¬ (c3_kind ≥ (2 : Int))) ↔ (¬ (¬ ((c3_kind) ≤ (1 : Int)))) := (not_congr (normalization_6836 c3_kind))

theorem normalization_6838 (c3_kind : Int) : ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))) ↔ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))) := (or_congr (normalization_6835 c3_kind) (normalization_6837 c3_kind))

theorem normalization_6839 (c3_kind : Int) : (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int)))))) := (not_congr (normalization_6838 c3_kind))

abbrev shared_expr_Classification078_6 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification078_5 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
theorem normalization_6840 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Classification078_6 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_6833 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_6839 c3_kind)))

theorem normalization_6841 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (¬ (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification078_6 c3_depth c3_kind c3_sign r1_group r1_level)) := (not_congr (normalization_6840 c3_depth c3_kind c3_sign r1_group r1_level))

theorem normalization_6842 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification078_6 c3_depth c3_kind c3_sign r1_group r1_level))) := (or_congr (normalization_59 r1_mode) (or_congr (normalization_60 r1_mode) (normalization_6841 c3_depth c3_kind c3_sign r1_group r1_level)))

theorem normalization_6843 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (formula_2022 c3_depth c3_kind c3_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification078_6 c3_depth c3_kind c3_sign r1_group r1_level)))) := (not_congr (normalization_6842 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

theorem normalization_6844 (c3_sign : Int) : (c3_sign ≤ (1 : Int)) ↔ ((c3_sign) ≤ (1 : Int)) := by
  omega

theorem normalization_6845 (c3_sign : Int) : (¬ (c3_sign ≤ (1 : Int))) ↔ (¬ ((c3_sign) ≤ (1 : Int))) := (not_congr (normalization_6844 c3_sign))

theorem normalization_6846 (c3_sign : Int) : (c3_sign ≥ (1 : Int)) ↔ (¬ ((c3_sign) ≤ (0 : Int))) := by
  omega

theorem normalization_6847 (c3_sign : Int) : (¬ (c3_sign ≥ (1 : Int))) ↔ (¬ (¬ ((c3_sign) ≤ (0 : Int)))) := (not_congr (normalization_6846 c3_sign))

theorem normalization_6848 (c3_sign : Int) : ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ↔ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) := (or_congr (normalization_6845 c3_sign) (normalization_6847 c3_sign))

theorem normalization_6849 (c3_sign : Int) : (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) := (not_congr (normalization_6848 c3_sign))

theorem normalization_6850 (c3_sign : Int) : ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) := (or_congr (normalization_6849 c3_sign) (normalization_6825 c3_sign))

theorem normalization_6851 (c3_sign : Int) : (¬ ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_6850 c3_sign))

abbrev shared_expr_Classification078_7 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_6852 (c3_depth c3_kind c3_sign r1_level : Int) : (formula_2023 c3_depth c3_kind c3_sign r1_level) ↔ (shared_expr_Classification078_7 c3_depth c3_kind c3_sign r1_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6851 c3_sign) (or_congr (normalization_6829 c3_depth r1_level) (normalization_6831 c3_depth r1_level)))))

theorem normalization_6853 (c3_depth c3_kind c3_sign r1_level : Int) : (¬ (formula_2023 c3_depth c3_kind c3_sign r1_level)) ↔ (¬ (shared_expr_Classification078_7 c3_depth c3_kind c3_sign r1_level)) := (not_congr (normalization_6852 c3_depth c3_kind c3_sign r1_level))

abbrev shared_expr_Classification078_8 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification078_7 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
theorem normalization_6854 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (formula_2024 c3_depth c3_kind c3_sign r1_group r1_level) ↔ (shared_expr_Classification078_8 c3_depth c3_kind c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_6853 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_6839 c3_kind)))

theorem normalization_6855 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : (¬ (formula_2024 c3_depth c3_kind c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification078_8 c3_depth c3_kind c3_sign r1_group r1_level)) := (not_congr (normalization_6854 c3_depth c3_kind c3_sign r1_group r1_level))

theorem normalization_6856 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2024 c3_depth c3_kind c3_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification078_8 c3_depth c3_kind c3_sign r1_group r1_level))) := (or_congr (normalization_5970 r1_mode) (or_congr (normalization_5972 r1_mode) (normalization_6855 c3_depth c3_kind c3_sign r1_group r1_level)))

theorem normalization_6857 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2024 c3_depth c3_kind c3_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification078_8 c3_depth c3_kind c3_sign r1_group r1_level)))) := (not_congr (normalization_6856 c3_depth c3_kind c3_sign r1_group r1_level r1_mode))

theorem normalization_6858 (c3_node : Int) : ((c3_node % (2 : Int)) ≤ (0 : Int)) ↔ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6859 (c3_node : Int) : (¬ ((c3_node % (2 : Int)) ≤ (0 : Int))) ↔ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6858 c3_node))

theorem normalization_6860 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_6861 (c3_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_6860 c3_depth r1_level))

theorem normalization_6862 (c3_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6863 (c3_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_6862 c3_depth r1_level))

abbrev shared_expr_Classification078_9 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_6864 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (formula_2025 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Classification078_9 c3_depth c3_kind c3_node c3_sign r1_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6827 c3_sign) (or_congr (normalization_6859 c3_node) (or_congr (normalization_6861 c3_depth r1_level) (normalization_6863 c3_depth r1_level))))))

theorem normalization_6865 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (¬ (formula_2025 c3_depth c3_kind c3_node c3_sign r1_level)) ↔ (¬ (shared_expr_Classification078_9 c3_depth c3_kind c3_node c3_sign r1_level)) := (not_congr (normalization_6864 c3_depth c3_kind c3_node c3_sign r1_level))

abbrev shared_expr_Classification078_10 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification078_9 c3_depth c3_kind c3_node c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification078_5 c3_depth c3_kind c3_sign r1_level))))
theorem normalization_6866 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2026 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Classification078_10 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_6865 c3_depth c3_kind c3_node c3_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_6833 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_6867 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (¬ (formula_2026 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification078_10 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (not_congr (normalization_6866 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

theorem normalization_6868 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2026 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification078_10 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := (or_congr (normalization_5980 r1_mode) (or_congr (normalization_5982 r1_mode) (normalization_6867 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))

theorem normalization_6869 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2026 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification078_10 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) := (not_congr (normalization_6868 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

theorem normalization_6870 (c3_node : Int) : ((c3_node % (2 : Int)) ≥ (1 : Int)) ↔ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) := by
  omega

theorem normalization_6871 (c3_node : Int) : (¬ ((c3_node % (2 : Int)) ≥ (1 : Int))) ↔ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := (not_congr (normalization_6870 c3_node))

abbrev shared_expr_Classification078_11 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_6872 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (formula_2027 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Classification078_11 c3_depth c3_kind c3_node c3_sign r1_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6827 c3_sign) (or_congr (normalization_6871 c3_node) (or_congr (normalization_6861 c3_depth r1_level) (normalization_6863 c3_depth r1_level))))))

theorem normalization_6873 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (¬ (formula_2027 c3_depth c3_kind c3_node c3_sign r1_level)) ↔ (¬ (shared_expr_Classification078_11 c3_depth c3_kind c3_node c3_sign r1_level)) := (not_congr (normalization_6872 c3_depth c3_kind c3_node c3_sign r1_level))

abbrev shared_expr_Classification078_12 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification078_11 c3_depth c3_kind c3_node c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification078_5 c3_depth c3_kind c3_sign r1_level))))
theorem normalization_6874 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2028 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Classification078_12 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_6873 c3_depth c3_kind c3_node c3_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_6833 c3_depth c3_kind c3_sign r1_level)))

theorem normalization_6875 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (¬ (formula_2028 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification078_12 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (not_congr (normalization_6874 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

theorem normalization_6876 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2028 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification078_12 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := (or_congr (normalization_5994 r1_mode) (or_congr (normalization_5996 r1_mode) (normalization_6875 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))

theorem normalization_6877 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2028 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification078_12 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) := (not_congr (normalization_6876 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

abbrev shared_expr_Classification078_13 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_6878 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (formula_2029 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Classification078_13 c3_depth c3_kind c3_node c3_sign r1_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6851 c3_sign) (or_congr (normalization_6859 c3_node) (or_congr (normalization_6861 c3_depth r1_level) (normalization_6863 c3_depth r1_level))))))

theorem normalization_6879 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (¬ (formula_2029 c3_depth c3_kind c3_node c3_sign r1_level)) ↔ (¬ (shared_expr_Classification078_13 c3_depth c3_kind c3_node c3_sign r1_level)) := (not_congr (normalization_6878 c3_depth c3_kind c3_node c3_sign r1_level))

abbrev shared_expr_Classification078_14 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification078_7 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification078_13 c3_depth c3_kind c3_node c3_sign r1_level))))
theorem normalization_6880 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2030 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Classification078_14 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_6853 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_6879 c3_depth c3_kind c3_node c3_sign r1_level)))

theorem normalization_6881 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (¬ (formula_2030 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification078_14 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (not_congr (normalization_6880 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

theorem normalization_6882 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2030 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification078_14 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := (or_congr (normalization_6004 r1_mode) (or_congr (normalization_6005 r1_mode) (normalization_6881 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))

theorem normalization_6883 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2030 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification078_14 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) := (not_congr (normalization_6882 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

abbrev shared_expr_Classification078_15 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_6884 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (formula_2031 c3_depth c3_kind c3_node c3_sign r1_level) ↔ (shared_expr_Classification078_15 c3_depth c3_kind c3_node c3_sign r1_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6851 c3_sign) (or_congr (normalization_6871 c3_node) (or_congr (normalization_6861 c3_depth r1_level) (normalization_6863 c3_depth r1_level))))))

theorem normalization_6885 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : (¬ (formula_2031 c3_depth c3_kind c3_node c3_sign r1_level)) ↔ (¬ (shared_expr_Classification078_15 c3_depth c3_kind c3_node c3_sign r1_level)) := (not_congr (normalization_6884 c3_depth c3_kind c3_node c3_sign r1_level))

abbrev shared_expr_Classification078_16 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification078_7 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification078_15 c3_depth c3_kind c3_node c3_sign r1_level))))
theorem normalization_6886 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (formula_2032 c3_depth c3_kind c3_node c3_sign r1_group r1_level) ↔ (shared_expr_Classification078_16 c3_depth c3_kind c3_node c3_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_6853 c3_depth c3_kind c3_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_6885 c3_depth c3_kind c3_node c3_sign r1_level)))

theorem normalization_6887 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : (¬ (formula_2032 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification078_16 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) := (not_congr (normalization_6886 c3_depth c3_kind c3_node c3_sign r1_group r1_level))

theorem normalization_6888 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2032 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification078_16 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := (or_congr (normalization_6013 r1_mode) (or_congr (normalization_6015 r1_mode) (normalization_6887 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))

theorem normalization_6889 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2032 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification078_16 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) := (not_congr (normalization_6888 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

abbrev shared_expr_Classification078_17 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification078_6 c3_depth c3_kind c3_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification078_8 c3_depth c3_kind c3_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification078_10 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification078_12 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification078_14 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification078_16 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))))
theorem normalization_6890 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2033 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_17 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := (or_congr (normalization_6843 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (or_congr (normalization_6857 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (or_congr (normalization_6869 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (or_congr (normalization_6877 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (or_congr (normalization_6883 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (normalization_6889 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))))))

abbrev shared_expr_Classification078_18 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification078_19 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification078_18 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification078_20 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification078_21 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification078_20 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification078_22 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification078_23 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification078_18 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification078_22 c3_depth c3_kind c3_node c3_sign r1_level)))
abbrev shared_expr_Classification078_24 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification078_25 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification078_18 c3_depth c3_kind c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification078_24 c3_depth c3_kind c3_node c3_sign r1_level)))
abbrev shared_expr_Classification078_26 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification078_27 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification078_26 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification078_20 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification078_28 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification078_29 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification078_28 c3_depth c3_kind c3_node c3_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification078_20 c3_depth c3_kind c3_sign r1_level)))
abbrev shared_expr_Classification078_30 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification078_19 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification078_21 c3_depth c3_kind c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification078_23 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification078_25 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification078_27 c3_depth c3_kind c3_node c3_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification078_29 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))
theorem normalization_6891 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : ((formula_2113 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (formula_2033 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) ↔ ((shared_expr_Classification078_30 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_17 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) := (iff_congr (normalization_6709 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (normalization_6890 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))

abbrev shared_expr_Classification078_31 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification078_1 c3_group c3_level c3_mode r1_group r1_level r1_mode))) ∨ ((¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification078_17 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
theorem normalization_6892 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2129 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_31 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_6746 c3_kind) (normalization_6807 c3_group c3_level c3_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_6746 c3_kind)) (normalization_6890 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))

abbrev shared_expr_Classification078_32 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification078_0 c3_group c3_level c3_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification078_30 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)))
abbrev shared_expr_Classification078_33 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((shared_expr_Classification078_32 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_31 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))
theorem normalization_6893 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2130 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_33 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_6710 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) (normalization_6892 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_4952 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2130 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_1784 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification078_0 c3_group c3_level c3_mode r1_group r1_level r1_mode) (shared_expr_Classification078_1 c3_group c3_level c3_mode r1_group r1_level r1_mode) (shared_expr_Classification078_30 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (shared_expr_Classification078_17 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))
  have n0 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6748 c3_kind) (replay_4923 c3_kind)
  have n1 : ((shared_expr_Classification078_0 c3_group c3_level c3_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Classification078_1 c3_group c3_level c3_mode r1_group r1_level r1_mode))) := by
    exact Iff.mp (normalization_6809 c3_group c3_level c3_mode r1_group r1_level r1_mode) (replay_4950 c3_group c3_level c3_mode r1_group r1_level r1_mode)
  have n2 : ((shared_expr_Classification078_30 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_17 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) := by
    exact Iff.mp (normalization_6891 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (replay_4951 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6893 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Classification078_34 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((formula_2129 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (formula_2035 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))
abbrev formula_2131 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification078_34 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)

theorem normalized_1785 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_35 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification078_17 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) ∨ ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification078_1 c3_group c3_level c3_mode r1_group r1_level r1_mode))))
theorem normalization_6894 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2035 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_35 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_6745 c3_kind) (normalization_6890 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_6745 c3_kind)) (normalization_6807 c3_group c3_level c3_mode r1_group r1_level r1_mode)))

abbrev shared_expr_Classification078_36 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((shared_expr_Classification078_31 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_35 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))
theorem normalization_6895 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2131 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_36 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_6892 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) (normalization_6894 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_4953 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2131 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_1785 ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification078_1 c3_group c3_level c3_mode r1_group r1_level r1_mode) (shared_expr_Classification078_17 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode))
  have hn := ht
  exact Iff.mpr (normalization_6895 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Classification078_37 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((formula_2114 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (formula_2035 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))
abbrev formula_2132 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification078_37 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)

theorem normalized_1786 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_38 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((shared_expr_Classification078_32 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_35 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))
theorem normalization_6896 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2132 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification078_38 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := (iff_congr (normalization_6710 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) (normalization_6894 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_4954 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2132 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_1786 (shared_expr_Classification078_32 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) (shared_expr_Classification078_31 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) (shared_expr_Classification078_35 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode))
  have n0 : (shared_expr_Classification078_33 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_6893 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) (replay_4952 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Classification078_36 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_6895 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) (replay_4953 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6896 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r1_group r1_level r1_mode) hn

-- Checked replay of rewrite.
theorem replay_4955 (c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign : Int) : ((formula_2117 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign) ↔ (formula_2057 c3_group c3_level c3_mode r1_depth r1_kind r1_node r1_sign)) := by
  classical
  first
  | (simp only [formula_2117, shared_expr_Classification077_89, formula_2115, shared_expr_Classification077_87, formula_2116, shared_expr_Classification077_88, formula_2091, shared_expr_Classification076_74, formula_2092, shared_expr_Classification076_75, formula_2093, shared_expr_Classification076_76, formula_2094, shared_expr_Classification076_77, formula_2057, shared_expr_Classification076_40, formula_2045, shared_expr_Classification076_28, formula_2043, shared_expr_Classification076_26, formula_2044, shared_expr_Classification076_27, formula_2048, shared_expr_Classification076_31, formula_2046, shared_expr_Classification076_29, formula_2047, shared_expr_Classification076_30, formula_2050, shared_expr_Classification076_33, formula_2049, shared_expr_Classification076_32, formula_2052, shared_expr_Classification076_35, formula_2051, shared_expr_Classification076_34, formula_2054, shared_expr_Classification076_37, formula_2053, shared_expr_Classification076_36, formula_2056, shared_expr_Classification076_39, formula_2055, shared_expr_Classification076_38, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_1787 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6897 (c3_kind : Int) : ((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int))) ↔ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) := (and_congr (normalization_6834 c3_kind) (normalization_6836 c3_kind))

theorem normalization_6898 (c3_kind : Int) : ((c3_kind = (2 : Int)) ↔ ((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int)))) ↔ ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) := (iff_congr (normalization_6545 c3_kind) (normalization_6897 c3_kind))

-- Checked replay of rewrite.
theorem replay_4956 (c3_kind : Int) : ((c3_kind = (2 : Int)) ↔ ((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_1787 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6898 c3_kind) hn

theorem normalized_1788 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6899 (c3_kind : Int) : (((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_6897 c3_kind) (normalization_6839 c3_kind))

-- Checked replay of rewrite.
theorem replay_4957 (c3_kind : Int) : (((c3_kind ≤ (2 : Int)) ∧ (c3_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_1788 ((c3_kind) ≤ (2 : Int)) ((c3_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6899 c3_kind) hn

theorem normalized_1789 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6900 (c3_kind : Int) : ((c3_kind = (2 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ↔ ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_6545 c3_kind) (normalization_6839 c3_kind))

-- Checked replay of trans.
theorem replay_4958 (c3_kind : Int) : ((c3_kind = (2 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_1789 (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
  have n0 : ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_6898 c3_kind) (replay_4956 c3_kind)
  have n1 : ((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6899 c3_kind) (replay_4957 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6900 c3_kind) hn

theorem normalized_1790 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6901 (c3_depth r1_depth : Int) : (r1_depth ≤ c3_depth) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6902 (c3_depth r1_depth : Int) : (r1_depth ≥ c3_depth) ↔ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6903 (c3_depth r1_depth : Int) : ((r1_depth ≤ c3_depth) ∧ (r1_depth ≥ c3_depth)) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (and_congr (normalization_6901 c3_depth r1_depth) (normalization_6902 c3_depth r1_depth))

abbrev shared_expr_Classification078_39 (c3_depth r1_depth : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
theorem normalization_6904 (c3_depth r1_depth : Int) : ((r1_depth = c3_depth) ↔ ((r1_depth ≤ c3_depth) ∧ (r1_depth ≥ c3_depth))) ↔ (shared_expr_Classification078_39 c3_depth r1_depth) := (iff_congr (normalization_6609 c3_depth r1_depth) (normalization_6903 c3_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_4959 (c3_depth r1_depth : Int) : ((r1_depth = c3_depth) ↔ ((r1_depth ≤ c3_depth) ∧ (r1_depth ≥ c3_depth))) := by
  classical
  have ht := (normalized_1790 ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6904 c3_depth r1_depth) hn

theorem normalized_1791 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6905 (c3_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6906 (c3_depth r1_depth : Int) : ((r1_depth ≤ c3_depth) ↔ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_6901 c3_depth r1_depth) (normalization_6905 c3_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_4960 (c3_depth r1_depth : Int) : ((r1_depth ≤ c3_depth) ↔ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1791 ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6906 c3_depth r1_depth) hn

theorem normalized_1792 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6907 (c3_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6908 (c3_depth r1_depth : Int) : ((r1_depth ≥ c3_depth) ↔ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (iff_congr (normalization_6902 c3_depth r1_depth) (normalization_6907 c3_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_4961 (c3_depth r1_depth : Int) : ((r1_depth ≥ c3_depth) ↔ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1792 ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6908 c3_depth r1_depth) hn

theorem normalized_1793 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6909 (c3_depth r1_depth : Int) : (((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (and_congr (normalization_6905 c3_depth r1_depth) (normalization_6907 c3_depth r1_depth))

theorem normalization_6910 (c3_depth r1_depth : Int) : (((r1_depth ≤ c3_depth) ∧ (r1_depth ≥ c3_depth)) ↔ (((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification078_39 c3_depth r1_depth) := (iff_congr (normalization_6903 c3_depth r1_depth) (normalization_6909 c3_depth r1_depth))

-- Checked replay of monotonicity.
theorem replay_4962 (c3_depth r1_depth : Int) : (((r1_depth ≤ c3_depth) ∧ (r1_depth ≥ c3_depth)) ↔ (((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1793 ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6906 c3_depth r1_depth) (replay_4960 c3_depth r1_depth)
  have n1 : (((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6908 c3_depth r1_depth) (replay_4961 c3_depth r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6910 c3_depth r1_depth) hn

abbrev shared_expr_Classification078_40 (c3_depth r1_depth : Int) : Prop := ((((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))))
abbrev formula_2133 (c3_depth r1_depth : Int) : Prop := (shared_expr_Classification078_40 c3_depth r1_depth)

theorem normalized_1794 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6911 (c3_depth r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_6905 c3_depth r1_depth))

theorem normalization_6912 (c3_depth r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (not_congr (normalization_6907 c3_depth r1_depth))

theorem normalization_6913 (c3_depth r1_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := (or_congr (normalization_6911 c3_depth r1_depth) (normalization_6912 c3_depth r1_depth))

theorem normalization_6914 (c3_depth r1_depth : Int) : (¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))) := (not_congr (normalization_6913 c3_depth r1_depth))

abbrev shared_expr_Classification078_41 (c3_depth r1_depth : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))))
theorem normalization_6915 (c3_depth r1_depth : Int) : (formula_2133 c3_depth r1_depth) ↔ (shared_expr_Classification078_41 c3_depth r1_depth) := (iff_congr (normalization_6909 c3_depth r1_depth) (normalization_6914 c3_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_4963 (c3_depth r1_depth : Int) : (formula_2133 c3_depth r1_depth) := by
  classical
  have ht := (normalized_1794 ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6915 c3_depth r1_depth) hn

theorem normalized_1795 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6916 (c3_depth r1_depth : Int) : (((r1_depth ≤ c3_depth) ∧ (r1_depth ≥ c3_depth)) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification078_41 c3_depth r1_depth) := (iff_congr (normalization_6903 c3_depth r1_depth) (normalization_6914 c3_depth r1_depth))

-- Checked replay of trans.
theorem replay_4964 (c3_depth r1_depth : Int) : (((r1_depth ≤ c3_depth) ∧ (r1_depth ≥ c3_depth)) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1795 ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (shared_expr_Classification078_41 c3_depth r1_depth))
  have n0 : (shared_expr_Classification078_39 c3_depth r1_depth) := by
    exact Iff.mp (normalization_6910 c3_depth r1_depth) (replay_4962 c3_depth r1_depth)
  have n1 : (shared_expr_Classification078_41 c3_depth r1_depth) := by
    exact Iff.mp (normalization_6915 c3_depth r1_depth) (replay_4963 c3_depth r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6916 c3_depth r1_depth) hn

theorem normalized_1796 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6917 (c3_depth r1_depth : Int) : ((r1_depth = c3_depth) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification078_41 c3_depth r1_depth) := (iff_congr (normalization_6609 c3_depth r1_depth) (normalization_6914 c3_depth r1_depth))

-- Checked replay of trans.
theorem replay_4965 (c3_depth r1_depth : Int) : ((r1_depth = c3_depth) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1796 ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (shared_expr_Classification078_41 c3_depth r1_depth))
  have n0 : (shared_expr_Classification078_39 c3_depth r1_depth) := by
    exact Iff.mp (normalization_6904 c3_depth r1_depth) (replay_4959 c3_depth r1_depth)
  have n1 : (shared_expr_Classification078_41 c3_depth r1_depth) := by
    exact Iff.mp (normalization_6916 c3_depth r1_depth) (replay_4964 c3_depth r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6917 c3_depth r1_depth) hn

theorem normalized_1797 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6918 (c3_sign : Int) : ((c3_sign ≤ (0 : Int)) ∧ (c3_sign ≥ (0 : Int))) ↔ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) := (and_congr (normalization_6814 c3_sign) (normalization_6816 c3_sign))

theorem normalization_6919 (c3_sign : Int) : ((c3_sign = (0 : Int)) ↔ ((c3_sign ≤ (0 : Int)) ∧ (c3_sign ≥ (0 : Int)))) ↔ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ↔ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int))))) := (iff_congr (normalization_6548 c3_sign) (normalization_6918 c3_sign))

-- Checked replay of rewrite.
theorem replay_4966 (c3_sign : Int) : ((c3_sign = (0 : Int)) ↔ ((c3_sign ≤ (0 : Int)) ∧ (c3_sign ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1797 (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6919 c3_sign) hn

theorem normalized_1798 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6920 (c3_sign : Int) : (((c3_sign ≤ (0 : Int)) ∧ (c3_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))))) ↔ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_6918 c3_sign) (normalization_6819 c3_sign))

-- Checked replay of rewrite.
theorem replay_4967 (c3_sign : Int) : (((c3_sign ≤ (0 : Int)) ∧ (c3_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1798 ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6920 c3_sign) hn

theorem normalized_1799 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6921 (c3_sign : Int) : ((c3_sign = (0 : Int)) ↔ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))))) ↔ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_6548 c3_sign) (normalization_6819 c3_sign))

-- Checked replay of trans.
theorem replay_4968 (c3_sign : Int) : ((c3_sign = (0 : Int)) ↔ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1799 (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))))))
  have n0 : ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ↔ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_6919 c3_sign) (replay_4966 c3_sign)
  have n1 : ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6920 c3_sign) (replay_4967 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6921 c3_sign) hn

abbrev shared_expr_Classification078_42 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((r1_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev formula_2134 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_42 c3_node c3_sign r1_node r1_sign)

theorem normalized_1800 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6922 (c3_node c3_sign r1_node r1_sign : Int) : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_113 r1_sign) (and_congr (normalization_6819 c3_sign) (normalization_6719 c3_node r1_node)))

abbrev shared_expr_Classification078_43 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ↔ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
theorem normalization_6923 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2134 c3_node c3_sign r1_node r1_sign) ↔ (shared_expr_Classification078_43 c3_node c3_sign r1_node r1_sign) := (iff_congr (normalization_6720 c3_node c3_sign r1_node r1_sign) (normalization_6922 c3_node c3_sign r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_4969 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2134 c3_node c3_sign r1_node r1_sign) := by
  classical
  have ht := (normalized_1800 (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))) (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))) ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have n0 : ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6049 r1_sign) (replay_2710 r1_sign)
  have n1 : ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6921 c3_sign) (replay_4968 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6923 c3_node c3_sign r1_node r1_sign) hn

abbrev shared_expr_Classification078_44 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))))
abbrev formula_2135 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_44 c3_node c3_sign r1_node r1_sign)

theorem normalized_1801 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4)) ↔ (¬ ((¬ (¬ p1)) ∨ (¬ p0) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6924 (c3_node r1_node : Int) : (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6719 c3_node r1_node))

theorem normalization_6925 (c3_node c3_sign r1_node r1_sign : Int) : ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) := (or_congr (normalization_73 r1_sign) (or_congr (normalization_75 r1_sign) (or_congr (normalization_6815 c3_sign) (or_congr (normalization_6817 c3_sign) (normalization_6924 c3_node r1_node)))))

theorem normalization_6926 (c3_node c3_sign r1_node r1_sign : Int) : (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_6925 c3_node c3_sign r1_node r1_sign))

abbrev shared_expr_Classification078_45 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))))
theorem normalization_6927 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2135 c3_node c3_sign r1_node r1_sign) ↔ (shared_expr_Classification078_45 c3_node c3_sign r1_node r1_sign) := (iff_congr (normalization_6922 c3_node c3_sign r1_node r1_sign) (normalization_6926 c3_node c3_sign r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_4970 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2135 c3_node c3_sign r1_node r1_sign) := by
  classical
  have ht := (normalized_1801 ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (-1 : Int)) ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6927 c3_node c3_sign r1_node r1_sign) hn

abbrev shared_expr_Classification078_46 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((r1_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))))
abbrev formula_2136 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_46 c3_node c3_sign r1_node r1_sign)

theorem normalized_1802 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_47 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))))
theorem normalization_6928 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2136 c3_node c3_sign r1_node r1_sign) ↔ (shared_expr_Classification078_47 c3_node c3_sign r1_node r1_sign) := (iff_congr (normalization_6720 c3_node c3_sign r1_node r1_sign) (normalization_6926 c3_node c3_sign r1_node r1_sign))

-- Checked replay of trans.
theorem replay_4971 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2136 c3_node c3_sign r1_node r1_sign) := by
  classical
  have ht := (normalized_1802 ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))))
  have n0 : (shared_expr_Classification078_43 c3_node c3_sign r1_node r1_sign) := by
    exact Iff.mp (normalization_6923 c3_node c3_sign r1_node r1_sign) (replay_4969 c3_node c3_sign r1_node r1_sign)
  have n1 : (shared_expr_Classification078_45 c3_node c3_sign r1_node r1_sign) := by
    exact Iff.mp (normalization_6927 c3_node c3_sign r1_node r1_sign) (replay_4970 c3_node c3_sign r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6928 c3_node c3_sign r1_node r1_sign) hn

theorem normalized_1803 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6929 (c3_sign : Int) : ((c3_sign ≤ (2 : Int)) ∧ (c3_sign ≥ (2 : Int))) ↔ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) := (and_congr (normalization_6820 c3_sign) (normalization_6822 c3_sign))

theorem normalization_6930 (c3_sign : Int) : ((c3_sign = (2 : Int)) ↔ ((c3_sign ≤ (2 : Int)) ∧ (c3_sign ≥ (2 : Int)))) ↔ ((((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ↔ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) := (iff_congr (normalization_6549 c3_sign) (normalization_6929 c3_sign))

-- Checked replay of rewrite.
theorem replay_4972 (c3_sign : Int) : ((c3_sign = (2 : Int)) ↔ ((c3_sign ≤ (2 : Int)) ∧ (c3_sign ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_1803 (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6930 c3_sign) hn

theorem normalized_1804 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6931 (c3_sign : Int) : (((c3_sign ≤ (2 : Int)) ∧ (c3_sign ≥ (2 : Int))) ↔ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ↔ ((((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_6929 c3_sign) (normalization_6825 c3_sign))

-- Checked replay of rewrite.
theorem replay_4973 (c3_sign : Int) : (((c3_sign ≤ (2 : Int)) ∧ (c3_sign ≥ (2 : Int))) ↔ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_1804 ((c3_sign) ≤ (2 : Int)) ((c3_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6931 c3_sign) hn

theorem normalized_1805 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6932 (c3_sign : Int) : ((c3_sign = (2 : Int)) ↔ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ↔ ((((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_6549 c3_sign) (normalization_6825 c3_sign))

-- Checked replay of trans.
theorem replay_4974 (c3_sign : Int) : ((c3_sign = (2 : Int)) ↔ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_1805 (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ((((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))))
  have n0 : ((((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ↔ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_6930 c3_sign) (replay_4972 c3_sign)
  have n1 : ((((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6931 c3_sign) (replay_4973 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6932 c3_sign) hn

abbrev shared_expr_Classification078_48 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))))) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
abbrev formula_2137 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_48 c3_node c3_sign h r1_depth r1_node r1_sign)

theorem normalized_1806 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∧ p2 ∧ p4 ∧ (¬ p6)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p5) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_49 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
theorem normalization_6933 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2137 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_49 c3_node c3_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_126 r1_sign) (and_congr (normalization_6825 c3_sign) (and_congr (normalization_6068 h r1_depth) (normalization_6719 c3_node r1_node))))

abbrev shared_expr_Classification078_50 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ∧ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
theorem normalization_6934 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (((r1_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (formula_2137 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification078_50 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_49 c3_node c3_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_6721 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6933 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification078_51 (h r1_depth : Int) : Prop := (((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))))))
theorem replay_4975 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (((r1_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (formula_2137 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1806 (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))) (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))) ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have n0 : ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6060 r1_sign) (replay_2716 r1_sign)
  have n1 : ((((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6932 c3_sign) (replay_4974 c3_sign)
  have n2 : (shared_expr_Classification078_51 h r1_depth) := by
    exact Iff.mp (normalization_6071 h r1_depth) (replay_2723 h r1_depth)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6934 c3_node c3_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1807 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ ((¬ p4) ∨ (¬ (¬ p5)))) ∧ (¬ p6)) ↔ (¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p6))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_52 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))) ∨ (¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
theorem normalization_6935 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_110 h r1_depth) (or_congr (normalization_104 h r1_depth) (or_congr (normalization_122 r1_sign) (or_congr (normalization_124 r1_sign) (or_congr (normalization_6821 c3_sign) (or_congr (normalization_6823 c3_sign) (normalization_6924 c3_node r1_node)))))))

theorem normalization_6936 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (¬ (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ (¬ (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign)) := (not_congr (normalization_6935 c3_node c3_sign h r1_depth r1_node r1_sign))

theorem normalization_6937 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2137 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign))) ↔ ((shared_expr_Classification078_49 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_6933 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6936 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_4976 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2137 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
  classical
  have ht := (normalized_1807 ((r1_sign) ≤ (2 : Int)) ((r1_sign) ≤ (1 : Int)) ((c3_sign) ≤ (2 : Int)) ((c3_sign) ≤ (1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6937 c3_node c3_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1808 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6938 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (((r1_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign))) ↔ ((shared_expr_Classification078_50 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_6721 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6936 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of trans.
theorem replay_4977 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (((r1_sign = (2 : Int)) ∧ (c3_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
  classical
  have ht := (normalized_1808 (shared_expr_Classification078_50 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_49 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign))
  have n0 : ((shared_expr_Classification078_50 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_49 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6934 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4975 c3_node c3_sign h r1_depth r1_node r1_sign)
  have n1 : ((shared_expr_Classification078_49 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6937 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4976 c3_node c3_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6938 c3_node c3_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1809 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6939 (c3_sign : Int) : ((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int))) ↔ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) := (and_congr (normalization_6844 c3_sign) (normalization_6846 c3_sign))

theorem normalization_6940 (c3_sign : Int) : ((c3_sign = (1 : Int)) ↔ ((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int)))) ↔ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) := (iff_congr (normalization_6554 c3_sign) (normalization_6939 c3_sign))

-- Checked replay of rewrite.
theorem replay_4978 (c3_sign : Int) : ((c3_sign = (1 : Int)) ↔ ((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1809 (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6940 c3_sign) hn

theorem normalized_1810 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6941 (c3_sign : Int) : (((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int))) ↔ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_6939 c3_sign) (normalization_6849 c3_sign))

-- Checked replay of rewrite.
theorem replay_4979 (c3_sign : Int) : (((c3_sign ≤ (1 : Int)) ∧ (c3_sign ≥ (1 : Int))) ↔ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1810 ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6941 c3_sign) hn

theorem normalized_1811 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6942 (c3_sign : Int) : ((c3_sign = (1 : Int)) ↔ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) ↔ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_6554 c3_sign) (normalization_6849 c3_sign))

-- Checked replay of trans.
theorem replay_4980 (c3_sign : Int) : ((c3_sign = (1 : Int)) ↔ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1811 (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))))
  have n0 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_6940 c3_sign) (replay_4978 c3_sign)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6941 c3_sign) (replay_4979 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6942 c3_sign) hn

abbrev shared_expr_Classification078_53 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))
abbrev formula_2138 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_53 c3_node c3_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Classification078_54 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_sign = (1 : Int)) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (formula_2138 c3_node c3_sign h r1_depth r1_node r1_sign))
abbrev formula_2139 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_54 c3_node c3_sign h r1_depth r1_node r1_sign)

theorem normalized_1812 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4) ∧ (¬ p5)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4) ∧ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_55 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
theorem normalization_6943 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2138 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_55 c3_node c3_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_119 r1_sign) (and_congr (normalization_6849 c3_sign) (and_congr (normalization_110 h r1_depth) (normalization_6723 c3_node r1_node))))

abbrev shared_expr_Classification078_56 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
theorem normalization_6944 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2139 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ ((shared_expr_Classification078_56 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_55 c3_node c3_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_6724 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6943 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_4981 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2139 c3_node c3_sign h r1_depth r1_node r1_sign) := by
  classical
  have ht := (normalized_1812 (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)))
  have n0 : ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6081 r1_sign) (replay_2729 r1_sign)
  have n1 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6942 c3_sign) (replay_4980 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6944 c3_node c3_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1813 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4) ∧ (¬ p5)) ↔ (¬ (p4 ∨ p5 ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_57 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∨ ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∨ (¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))
theorem normalization_6945 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_109 h r1_depth) (or_congr (normalization_6722 c3_node r1_node) (or_congr (normalization_115 r1_sign) (or_congr (normalization_117 r1_sign) (or_congr (normalization_6845 c3_sign) (normalization_6847 c3_sign))))))

theorem normalization_6946 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (¬ (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ (¬ (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign)) := (not_congr (normalization_6945 c3_node c3_sign h r1_depth r1_node r1_sign))

theorem normalization_6947 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2138 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign))) ↔ ((shared_expr_Classification078_55 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_6943 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6946 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_4982 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2138 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
  classical
  have ht := (normalized_1813 ((r1_sign) ≤ (1 : Int)) ((r1_sign) ≤ (0 : Int)) ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6947 c3_node c3_sign h r1_depth r1_node r1_sign) hn

abbrev shared_expr_Classification078_58 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_sign = (1 : Int)) ∧ (c3_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ↔ (¬ (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign)))
abbrev formula_2140 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_58 c3_node c3_sign h r1_depth r1_node r1_sign)

theorem normalized_1814 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6948 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2140 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ ((shared_expr_Classification078_56 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_6724 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6946 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of trans.
theorem replay_4983 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2140 c3_node c3_sign h r1_depth r1_node r1_sign) := by
  classical
  have ht := (normalized_1814 (shared_expr_Classification078_56 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_55 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign))
  have n0 : ((shared_expr_Classification078_56 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_55 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6944 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4981 c3_node c3_sign h r1_depth r1_node r1_sign)
  have n1 : ((shared_expr_Classification078_55 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6947 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4982 c3_node c3_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6948 c3_node c3_sign h r1_depth r1_node r1_sign) hn

abbrev shared_expr_Classification078_59 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign)))
abbrev formula_2141 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_59 c3_node c3_sign h r1_depth r1_node r1_sign)

theorem normalized_1815 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∨ p2 ∨ p4) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_60 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (¬ (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign)))
theorem normalization_6949 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2141 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_60 c3_node c3_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_6926 c3_node c3_sign r1_node r1_sign) (or_congr (normalization_6936 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6946 c3_node c3_sign h r1_depth r1_node r1_sign)))

abbrev shared_expr_Classification078_61 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification078_50 c3_node c3_sign h r1_depth r1_node r1_sign) ∨ (shared_expr_Classification078_56 c3_node c3_sign h r1_depth r1_node r1_sign))
theorem normalization_6950 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2118 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (formula_2141 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification078_61 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_60 c3_node c3_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_6725 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6949 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_4984 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2118 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (formula_2141 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1815 ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) (shared_expr_Classification078_50 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_56 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign))
  have n0 : (shared_expr_Classification078_47 c3_node c3_sign r1_node r1_sign) := by
    exact Iff.mp (normalization_6928 c3_node c3_sign r1_node r1_sign) (replay_4971 c3_node c3_sign r1_node r1_sign)
  have n1 : ((shared_expr_Classification078_50 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6938 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4977 c3_node c3_sign h r1_depth r1_node r1_sign)
  have n2 : ((shared_expr_Classification078_56 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6948 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4983 c3_node c3_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6950 c3_node c3_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1816 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ↔ ((¬ p1) ∨ (¬ p0) ∨ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_62 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign)))
theorem normalization_6951 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_62 c3_node c3_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_6936 c3_node c3_sign h r1_depth r1_node r1_sign) (or_congr (normalization_6926 c3_node c3_sign r1_node r1_sign) (normalization_6946 c3_node c3_sign h r1_depth r1_node r1_sign)))

theorem normalization_6952 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2141 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification078_60 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_62 c3_node c3_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_6949 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6951 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_4985 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2141 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1816 ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) (shared_expr_Classification078_52 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_57 c3_node c3_sign h r1_depth r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_6952 c3_node c3_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1817 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6953 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2118 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification078_61 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_62 c3_node c3_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_6725 c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6951 c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of trans.
theorem replay_4986 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2118 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1817 (shared_expr_Classification078_61 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_60 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_62 c3_node c3_sign h r1_depth r1_node r1_sign))
  have n0 : ((shared_expr_Classification078_61 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_60 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6950 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4984 c3_node c3_sign h r1_depth r1_node r1_sign)
  have n1 : ((shared_expr_Classification078_60 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_62 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6952 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4985 c3_node c3_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6953 c3_node c3_sign h r1_depth r1_node r1_sign) hn

abbrev shared_expr_Classification078_63 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_depth = c3_depth) ∧ (formula_2118 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ ((¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ∧ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign)))
abbrev formula_2142 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification078_63 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)

theorem normalized_1818 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification078_64 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))) ∧ (shared_expr_Classification078_62 c3_node c3_sign h r1_depth r1_node r1_sign))
theorem normalization_6954 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ∧ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ (shared_expr_Classification078_64 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_6914 c3_depth r1_depth) (normalization_6951 c3_node c3_sign h r1_depth r1_node r1_sign))

abbrev shared_expr_Classification078_65 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification078_61 c3_node c3_sign h r1_depth r1_node r1_sign)) ↔ (shared_expr_Classification078_64 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign))
theorem normalization_6955 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2142 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_65 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) := (iff_congr (normalization_6726 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) (normalization_6954 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_4987 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2142 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) := by
  classical
  have ht := (normalized_1818 ((¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ((¬ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) (shared_expr_Classification078_61 c3_node c3_sign h r1_depth r1_node r1_sign) (shared_expr_Classification078_62 c3_node c3_sign h r1_depth r1_node r1_sign))
  have n0 : (shared_expr_Classification078_41 c3_depth r1_depth) := by
    exact Iff.mp (normalization_6917 c3_depth r1_depth) (replay_4965 c3_depth r1_depth)
  have n1 : ((shared_expr_Classification078_61 c3_node c3_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification078_62 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6953 c3_node c3_sign h r1_depth r1_node r1_sign) (replay_4986 c3_node c3_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6955 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) hn

end H4Formal.Generated.Classification
