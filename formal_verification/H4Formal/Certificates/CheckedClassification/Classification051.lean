import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification050

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_2668 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i180 : ((formula_1693 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (formula_1735 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2667 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2666 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i180)

theorem normalized_1390 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5898 (c0_mode r1_mode : Int) : (r1_mode ≤ c0_mode) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5899 (c0_mode r1_mode : Int) : (r1_mode ≥ c0_mode) ↔ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_5900 (c0_mode r1_mode : Int) : ((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (and_congr (normalization_5898 c0_mode r1_mode) (normalization_5899 c0_mode r1_mode))

abbrev shared_expr_Classification051_0 (c0_mode r1_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
theorem normalization_5901 (c0_mode r1_mode : Int) : ((r1_mode = c0_mode) ↔ ((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode))) ↔ (shared_expr_Classification051_0 c0_mode r1_mode) := (iff_congr (normalization_5704 c0_mode r1_mode) (normalization_5900 c0_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_2669 (c0_mode r1_mode : Int) : ((r1_mode = c0_mode) ↔ ((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode))) := by
  classical
  have ht := (normalized_1390 ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5901 c0_mode r1_mode) hn

theorem normalized_1391 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5902 (c0_mode r1_mode : Int) : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5903 (c0_mode r1_mode : Int) : ((r1_mode ≤ c0_mode) ↔ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ↔ ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_5898 c0_mode r1_mode) (normalization_5902 c0_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_2670 (c0_mode r1_mode : Int) : ((r1_mode ≤ c0_mode) ↔ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1391 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5903 c0_mode r1_mode) hn

theorem normalized_1392 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5904 (c0_mode r1_mode : Int) : ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_5905 (c0_mode r1_mode : Int) : ((r1_mode ≥ c0_mode) ↔ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ (((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (iff_congr (normalization_5899 c0_mode r1_mode) (normalization_5904 c0_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_2671 (c0_mode r1_mode : Int) : ((r1_mode ≥ c0_mode) ↔ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1392 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5905 c0_mode r1_mode) hn

theorem normalized_1393 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5906 (c0_mode r1_mode : Int) : (((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (and_congr (normalization_5902 c0_mode r1_mode) (normalization_5904 c0_mode r1_mode))

theorem normalization_5907 (c0_mode r1_mode : Int) : (((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ (((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Classification051_0 c0_mode r1_mode) := (iff_congr (normalization_5900 c0_mode r1_mode) (normalization_5906 c0_mode r1_mode))

-- Checked replay of monotonicity.
theorem replay_2672 (c0_mode r1_mode : Int) : (((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ (((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1393 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5903 c0_mode r1_mode) (replay_2670 c0_mode r1_mode)
  have n1 : (((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5905 c0_mode r1_mode) (replay_2671 c0_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5907 c0_mode r1_mode) hn

abbrev shared_expr_Classification051_1 (c0_mode r1_mode : Int) : Prop := ((((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))))
abbrev formula_1737 (c0_mode r1_mode : Int) : Prop := (shared_expr_Classification051_1 c0_mode r1_mode)

theorem normalized_1394 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5908 (c0_mode r1_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_5902 c0_mode r1_mode))

theorem normalization_5909 (c0_mode r1_mode : Int) : (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) := (not_congr (normalization_5904 c0_mode r1_mode))

theorem normalization_5910 (c0_mode r1_mode : Int) : ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))) := (or_congr (normalization_5908 c0_mode r1_mode) (normalization_5909 c0_mode r1_mode))

theorem normalization_5911 (c0_mode r1_mode : Int) : (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) := (not_congr (normalization_5910 c0_mode r1_mode))

abbrev shared_expr_Classification051_2 (c0_mode r1_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))))
theorem normalization_5912 (c0_mode r1_mode : Int) : (formula_1737 c0_mode r1_mode) ↔ (shared_expr_Classification051_2 c0_mode r1_mode) := (iff_congr (normalization_5906 c0_mode r1_mode) (normalization_5911 c0_mode r1_mode))

-- Checked replay of rewrite.
theorem replay_2673 (c0_mode r1_mode : Int) : (formula_1737 c0_mode r1_mode) := by
  classical
  have ht := (normalized_1394 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5912 c0_mode r1_mode) hn

theorem normalized_1395 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5913 (c0_mode r1_mode : Int) : (((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification051_2 c0_mode r1_mode) := (iff_congr (normalization_5900 c0_mode r1_mode) (normalization_5911 c0_mode r1_mode))

-- Checked replay of trans.
theorem replay_2674 (c0_mode r1_mode : Int) : (((r1_mode ≤ c0_mode) ∧ (r1_mode ≥ c0_mode)) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1395 ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) (shared_expr_Classification051_2 c0_mode r1_mode))
  have n0 : (shared_expr_Classification051_0 c0_mode r1_mode) := by
    exact Iff.mp (normalization_5907 c0_mode r1_mode) (replay_2672 c0_mode r1_mode)
  have n1 : (shared_expr_Classification051_2 c0_mode r1_mode) := by
    exact Iff.mp (normalization_5912 c0_mode r1_mode) (replay_2673 c0_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5913 c0_mode r1_mode) hn

theorem normalized_1396 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5914 (c0_mode r1_mode : Int) : ((r1_mode = c0_mode) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification051_2 c0_mode r1_mode) := (iff_congr (normalization_5704 c0_mode r1_mode) (normalization_5911 c0_mode r1_mode))

-- Checked replay of trans.
theorem replay_2675 (c0_mode r1_mode : Int) : ((r1_mode = c0_mode) ↔ (¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1396 ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) (shared_expr_Classification051_2 c0_mode r1_mode))
  have n0 : (shared_expr_Classification051_0 c0_mode r1_mode) := by
    exact Iff.mp (normalization_5901 c0_mode r1_mode) (replay_2669 c0_mode r1_mode)
  have n1 : (shared_expr_Classification051_2 c0_mode r1_mode) := by
    exact Iff.mp (normalization_5913 c0_mode r1_mode) (replay_2674 c0_mode r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5914 c0_mode r1_mode) hn

theorem normalized_1397 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5915 (c0_level r1_level : Int) : (r1_level ≤ c0_level) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5916 (c0_level r1_level : Int) : (r1_level ≥ c0_level) ↔ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5917 (c0_level r1_level : Int) : ((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (and_congr (normalization_5915 c0_level r1_level) (normalization_5916 c0_level r1_level))

abbrev shared_expr_Classification051_3 (c0_level r1_level : Int) : Prop := (((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
theorem normalization_5918 (c0_level r1_level : Int) : ((r1_level = c0_level) ↔ ((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level))) ↔ (shared_expr_Classification051_3 c0_level r1_level) := (iff_congr (normalization_5705 c0_level r1_level) (normalization_5917 c0_level r1_level))

-- Checked replay of rewrite.
theorem replay_2676 (c0_level r1_level : Int) : ((r1_level = c0_level) ↔ ((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level))) := by
  classical
  have ht := (normalized_1397 ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5918 c0_level r1_level) hn

theorem normalized_1398 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5919 (c0_level r1_level : Int) : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5920 (c0_level r1_level : Int) : ((r1_level ≤ c0_level) ↔ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_5915 c0_level r1_level) (normalization_5919 c0_level r1_level))

-- Checked replay of rewrite.
theorem replay_2677 (c0_level r1_level : Int) : ((r1_level ≤ c0_level) ↔ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1398 ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5920 c0_level r1_level) hn

theorem normalized_1399 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5921 (c0_level r1_level : Int) : ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5922 (c0_level r1_level : Int) : ((r1_level ≥ c0_level) ↔ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (iff_congr (normalization_5916 c0_level r1_level) (normalization_5921 c0_level r1_level))

-- Checked replay of rewrite.
theorem replay_2678 (c0_level r1_level : Int) : ((r1_level ≥ c0_level) ↔ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1399 ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5922 c0_level r1_level) hn

theorem normalized_1400 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5923 (c0_level r1_level : Int) : (((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (and_congr (normalization_5919 c0_level r1_level) (normalization_5921 c0_level r1_level))

theorem normalization_5924 (c0_level r1_level : Int) : (((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ (((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) ↔ (shared_expr_Classification051_3 c0_level r1_level) := (iff_congr (normalization_5917 c0_level r1_level) (normalization_5923 c0_level r1_level))

-- Checked replay of monotonicity.
theorem replay_2679 (c0_level r1_level : Int) : (((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ (((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1400 ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5920 c0_level r1_level) (replay_2677 c0_level r1_level)
  have n1 : (((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5922 c0_level r1_level) (replay_2678 c0_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5924 c0_level r1_level) hn

abbrev shared_expr_Classification051_4 (c0_level r1_level : Int) : Prop := ((((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))))
abbrev formula_1738 (c0_level r1_level : Int) : Prop := (shared_expr_Classification051_4 c0_level r1_level)

theorem normalized_1401 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5925 (c0_level r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5919 c0_level r1_level))

theorem normalization_5926 (c0_level r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_5921 c0_level r1_level))

theorem normalization_5927 (c0_level r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) := (or_congr (normalization_5925 c0_level r1_level) (normalization_5926 c0_level r1_level))

theorem normalization_5928 (c0_level r1_level : Int) : (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) := (not_congr (normalization_5927 c0_level r1_level))

abbrev shared_expr_Classification051_5 (c0_level r1_level : Int) : Prop := (((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))))
theorem normalization_5929 (c0_level r1_level : Int) : (formula_1738 c0_level r1_level) ↔ (shared_expr_Classification051_5 c0_level r1_level) := (iff_congr (normalization_5923 c0_level r1_level) (normalization_5928 c0_level r1_level))

-- Checked replay of rewrite.
theorem replay_2680 (c0_level r1_level : Int) : (formula_1738 c0_level r1_level) := by
  classical
  have ht := (normalized_1401 ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5929 c0_level r1_level) hn

theorem normalized_1402 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5930 (c0_level r1_level : Int) : (((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification051_5 c0_level r1_level) := (iff_congr (normalization_5917 c0_level r1_level) (normalization_5928 c0_level r1_level))

-- Checked replay of trans.
theorem replay_2681 (c0_level r1_level : Int) : (((r1_level ≤ c0_level) ∧ (r1_level ≥ c0_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1402 ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) (shared_expr_Classification051_5 c0_level r1_level))
  have n0 : (shared_expr_Classification051_3 c0_level r1_level) := by
    exact Iff.mp (normalization_5924 c0_level r1_level) (replay_2679 c0_level r1_level)
  have n1 : (shared_expr_Classification051_5 c0_level r1_level) := by
    exact Iff.mp (normalization_5929 c0_level r1_level) (replay_2680 c0_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5930 c0_level r1_level) hn

theorem normalized_1403 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5931 (c0_level r1_level : Int) : ((r1_level = c0_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification051_5 c0_level r1_level) := (iff_congr (normalization_5705 c0_level r1_level) (normalization_5928 c0_level r1_level))

-- Checked replay of trans.
theorem replay_2682 (c0_level r1_level : Int) : ((r1_level = c0_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1403 ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) (shared_expr_Classification051_5 c0_level r1_level))
  have n0 : (shared_expr_Classification051_3 c0_level r1_level) := by
    exact Iff.mp (normalization_5918 c0_level r1_level) (replay_2676 c0_level r1_level)
  have n1 : (shared_expr_Classification051_5 c0_level r1_level) := by
    exact Iff.mp (normalization_5930 c0_level r1_level) (replay_2681 c0_level r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5931 c0_level r1_level) hn

theorem normalized_1404 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5932 (c0_group r1_group : Int) : (r1_group ≤ c0_group) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5933 (c0_group r1_group : Int) : (r1_group ≥ c0_group) ↔ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_5934 (c0_group r1_group : Int) : ((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (and_congr (normalization_5932 c0_group r1_group) (normalization_5933 c0_group r1_group))

abbrev shared_expr_Classification051_6 (c0_group r1_group : Int) : Prop := (((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
theorem normalization_5935 (c0_group r1_group : Int) : ((r1_group = c0_group) ↔ ((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group))) ↔ (shared_expr_Classification051_6 c0_group r1_group) := (iff_congr (normalization_5785 c0_group r1_group) (normalization_5934 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2683 (c0_group r1_group : Int) : ((r1_group = c0_group) ↔ ((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group))) := by
  classical
  have ht := (normalized_1404 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5935 c0_group r1_group) hn

theorem normalized_1405 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5936 (c0_group r1_group : Int) : ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5937 (c0_group r1_group : Int) : ((r1_group ≤ c0_group) ↔ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_5932 c0_group r1_group) (normalization_5936 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2684 (c0_group r1_group : Int) : ((r1_group ≤ c0_group) ↔ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1405 ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5937 c0_group r1_group) hn

theorem normalized_1406 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5938 (c0_group r1_group : Int) : ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_5939 (c0_group r1_group : Int) : ((r1_group ≥ c0_group) ↔ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (iff_congr (normalization_5933 c0_group r1_group) (normalization_5938 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2685 (c0_group r1_group : Int) : ((r1_group ≥ c0_group) ↔ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1406 ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5939 c0_group r1_group) hn

theorem normalized_1407 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5940 (c0_group r1_group : Int) : (((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (and_congr (normalization_5936 c0_group r1_group) (normalization_5938 c0_group r1_group))

theorem normalization_5941 (c0_group r1_group : Int) : (((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ (((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) ↔ (shared_expr_Classification051_6 c0_group r1_group) := (iff_congr (normalization_5934 c0_group r1_group) (normalization_5940 c0_group r1_group))

-- Checked replay of monotonicity.
theorem replay_2686 (c0_group r1_group : Int) : (((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ (((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1407 ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5937 c0_group r1_group) (replay_2684 c0_group r1_group)
  have n1 : (((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5939 c0_group r1_group) (replay_2685 c0_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5941 c0_group r1_group) hn

abbrev shared_expr_Classification051_7 (c0_group r1_group : Int) : Prop := ((((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))
abbrev formula_1739 (c0_group r1_group : Int) : Prop := (shared_expr_Classification051_7 c0_group r1_group)

theorem normalized_1408 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5942 (c0_group r1_group : Int) : (¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_5936 c0_group r1_group))

theorem normalization_5943 (c0_group r1_group : Int) : (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) := (not_congr (normalization_5938 c0_group r1_group))

theorem normalization_5944 (c0_group r1_group : Int) : ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) := (or_congr (normalization_5942 c0_group r1_group) (normalization_5943 c0_group r1_group))

theorem normalization_5945 (c0_group r1_group : Int) : (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))) := (not_congr (normalization_5944 c0_group r1_group))

abbrev shared_expr_Classification051_8 (c0_group r1_group : Int) : Prop := (((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_5946 (c0_group r1_group : Int) : (formula_1739 c0_group r1_group) ↔ (shared_expr_Classification051_8 c0_group r1_group) := (iff_congr (normalization_5940 c0_group r1_group) (normalization_5945 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2687 (c0_group r1_group : Int) : (formula_1739 c0_group r1_group) := by
  classical
  have ht := (normalized_1408 ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5946 c0_group r1_group) hn

theorem normalized_1409 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5947 (c0_group r1_group : Int) : (((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification051_8 c0_group r1_group) := (iff_congr (normalization_5934 c0_group r1_group) (normalization_5945 c0_group r1_group))

-- Checked replay of trans.
theorem replay_2688 (c0_group r1_group : Int) : (((r1_group ≤ c0_group) ∧ (r1_group ≥ c0_group)) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1409 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) (shared_expr_Classification051_8 c0_group r1_group))
  have n0 : (shared_expr_Classification051_6 c0_group r1_group) := by
    exact Iff.mp (normalization_5941 c0_group r1_group) (replay_2686 c0_group r1_group)
  have n1 : (shared_expr_Classification051_8 c0_group r1_group) := by
    exact Iff.mp (normalization_5946 c0_group r1_group) (replay_2687 c0_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5947 c0_group r1_group) hn

theorem normalized_1410 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5948 (c0_group r1_group : Int) : ((r1_group = c0_group) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification051_8 c0_group r1_group) := (iff_congr (normalization_5785 c0_group r1_group) (normalization_5945 c0_group r1_group))

-- Checked replay of trans.
theorem replay_2689 (c0_group r1_group : Int) : ((r1_group = c0_group) ↔ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1410 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) (shared_expr_Classification051_8 c0_group r1_group))
  have n0 : (shared_expr_Classification051_6 c0_group r1_group) := by
    exact Iff.mp (normalization_5935 c0_group r1_group) (replay_2683 c0_group r1_group)
  have n1 : (shared_expr_Classification051_8 c0_group r1_group) := by
    exact Iff.mp (normalization_5947 c0_group r1_group) (replay_2688 c0_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5948 c0_group r1_group) hn

theorem normalized_1411 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5949 (c0_group r1_group : Int) : (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))) := (not_congr (normalization_5945 c0_group r1_group))

abbrev shared_expr_Classification051_9 (c0_group r1_group : Int) : Prop := ((¬ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))))
theorem normalization_5950 (c0_group r1_group : Int) : ((¬ (r1_group = c0_group)) ↔ (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Classification051_9 c0_group r1_group) := (iff_congr (normalization_5786 c0_group r1_group) (normalization_5949 c0_group r1_group))

-- Checked replay of monotonicity.
theorem replay_2690 (c0_group r1_group : Int) : ((¬ (r1_group = c0_group)) ↔ (¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1411 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification051_8 c0_group r1_group) := by
    exact Iff.mp (normalization_5948 c0_group r1_group) (replay_2689 c0_group r1_group)
  have hn := ht n0
  exact Iff.mpr (normalization_5950 c0_group r1_group) hn

abbrev shared_expr_Classification051_10 (c0_group r1_group : Int) : Prop := ((¬ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))
abbrev formula_1740 (c0_group r1_group : Int) : Prop := (shared_expr_Classification051_10 c0_group r1_group)

theorem normalized_1412 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification051_11 (c0_group r1_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_5951 (c0_group r1_group : Int) : (formula_1740 c0_group r1_group) ↔ (shared_expr_Classification051_11 c0_group r1_group) := (iff_congr (normalization_5949 c0_group r1_group) (normalization_5944 c0_group r1_group))

-- Checked replay of rewrite.
theorem replay_2691 (c0_group r1_group : Int) : (formula_1740 c0_group r1_group) := by
  classical
  have ht := (normalized_1412 ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5951 c0_group r1_group) hn

theorem normalized_1413 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification051_12 (c0_group r1_group : Int) : Prop := ((¬ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_5952 (c0_group r1_group : Int) : ((¬ (r1_group = c0_group)) ↔ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) ↔ (shared_expr_Classification051_12 c0_group r1_group) := (iff_congr (normalization_5786 c0_group r1_group) (normalization_5944 c0_group r1_group))

-- Checked replay of trans.
theorem replay_2692 (c0_group r1_group : Int) : ((¬ (r1_group = c0_group)) ↔ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1413 ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification051_9 c0_group r1_group) := by
    exact Iff.mp (normalization_5950 c0_group r1_group) (replay_2690 c0_group r1_group)
  have n1 : (shared_expr_Classification051_11 c0_group r1_group) := by
    exact Iff.mp (normalization_5951 c0_group r1_group) (replay_2691 c0_group r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5952 c0_group r1_group) hn

abbrev shared_expr_Classification051_13 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))) ∧ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))
abbrev formula_1741 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification051_13 c0_group c0_level c0_mode r1_group r1_level r1_mode)

theorem normalized_1414 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification051_14 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_5953 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (formula_1741 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_14 c0_group c0_level c0_mode r1_group r1_level r1_mode) := (and_congr (normalization_5911 c0_mode r1_mode) (and_congr (normalization_5928 c0_level r1_level) (normalization_5944 c0_group r1_group)))

abbrev shared_expr_Classification051_15 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
theorem normalization_5954 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group))) ↔ (formula_1741 c0_group c0_level c0_mode r1_group r1_level r1_mode)) ↔ ((shared_expr_Classification051_15 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_14 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := (iff_congr (normalization_5787 c0_group c0_level c0_mode r1_group r1_level r1_mode) (normalization_5953 c0_group c0_level c0_mode r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_2693 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group))) ↔ (formula_1741 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := by
  classical
  have ht := (normalized_1414 ((¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)))) ((¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ((¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) ((¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification051_2 c0_mode r1_mode) := by
    exact Iff.mp (normalization_5914 c0_mode r1_mode) (replay_2675 c0_mode r1_mode)
  have n1 : (shared_expr_Classification051_5 c0_level r1_level) := by
    exact Iff.mp (normalization_5931 c0_level r1_level) (replay_2682 c0_level r1_level)
  have n2 : (shared_expr_Classification051_12 c0_group r1_group) := by
    exact Iff.mp (normalization_5952 c0_group r1_group) (replay_2692 c0_group r1_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5954 c0_group c0_level c0_mode r1_group r1_level r1_mode) hn

theorem normalized_1415 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification051_16 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int))))))
theorem normalization_5955 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode) := (or_congr (normalization_5908 c0_mode r1_mode) (or_congr (normalization_5909 c0_mode r1_mode) (or_congr (normalization_5925 c0_level r1_level) (or_congr (normalization_5926 c0_level r1_level) (normalization_5945 c0_group r1_group)))))

theorem normalization_5956 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (¬ (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode)) ↔ (¬ (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := (not_congr (normalization_5955 c0_group c0_level c0_mode r1_group r1_level r1_mode))

theorem normalization_5957 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : ((formula_1741 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode))) ↔ ((shared_expr_Classification051_14 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := (iff_congr (normalization_5953 c0_group c0_level c0_mode r1_group r1_level r1_mode) (normalization_5956 c0_group c0_level c0_mode r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_2694 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : ((formula_1741 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := by
  classical
  have ht := (normalized_1415 ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((¬ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r1_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5957 c0_group c0_level c0_mode r1_group r1_level r1_mode) hn

theorem normalized_1416 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5958 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group))) ↔ (¬ (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode))) ↔ ((shared_expr_Classification051_15 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := (iff_congr (normalization_5787 c0_group c0_level c0_mode r1_group r1_level r1_mode) (normalization_5956 c0_group c0_level c0_mode r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_2695 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : (((r1_mode = c0_mode) ∧ (r1_level = c0_level) ∧ (¬ (r1_group = c0_group))) ↔ (¬ (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := by
  classical
  have ht := (normalized_1416 (shared_expr_Classification051_15 c0_group c0_level c0_mode r1_group r1_level r1_mode) (shared_expr_Classification051_14 c0_group c0_level c0_mode r1_group r1_level r1_mode) (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode))
  have n0 : ((shared_expr_Classification051_15 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_14 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := by
    exact Iff.mp (normalization_5954 c0_group c0_level c0_mode r1_group r1_level r1_mode) (replay_2693 c0_group c0_level c0_mode r1_group r1_level r1_mode)
  have n1 : ((shared_expr_Classification051_14 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := by
    exact Iff.mp (normalization_5957 c0_group c0_level c0_mode r1_group r1_level r1_mode) (replay_2694 c0_group c0_level c0_mode r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5958 c0_group c0_level c0_mode r1_group r1_level r1_mode) hn

-- Checked replay of rewrite.
theorem replay_2696 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((formula_1726 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (formula_1670 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) := by
  classical
  first
  | (simp only [formula_1726, shared_expr_Classification050_142, formula_1720, shared_expr_Classification050_136, formula_1721, shared_expr_Classification050_137, formula_1722, shared_expr_Classification050_138, formula_1723, shared_expr_Classification050_139, formula_1724, shared_expr_Classification050_140, formula_1725, shared_expr_Classification050_141, formula_1670, shared_expr_Classification050_12, formula_1659, shared_expr_Classification050_1, formula_1658, shared_expr_Classification050_0, formula_1661, shared_expr_Classification050_3, formula_1660, shared_expr_Classification050_2, formula_1663, shared_expr_Classification050_5, formula_1662, shared_expr_Classification050_4, formula_1665, shared_expr_Classification050_7, formula_1664, shared_expr_Classification050_6, formula_1667, shared_expr_Classification050_9, formula_1666, shared_expr_Classification050_8, formula_1669, shared_expr_Classification050_11, formula_1668, shared_expr_Classification050_10, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Classification051_17 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∧ (¬ (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode))) ∨ ((¬ (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) ∧ (formula_1670 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))
abbrev formula_1742 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification051_17 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)

abbrev shared_expr_Classification051_18 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((formula_1727 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (formula_1742 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))
abbrev formula_1743 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification051_18 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_1417 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5959 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_5960 (c0_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) := (not_congr (normalization_5959 c0_depth r1_level))

theorem normalization_5961 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5962 (c0_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := (not_congr (normalization_5961 c0_depth r1_level))

abbrev shared_expr_Classification051_19 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_5963 (c0_depth c0_kind c0_sign r1_level : Int) : (formula_1658 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Classification051_19 c0_depth c0_kind c0_sign r1_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5484 c0_sign) (or_congr (normalization_5960 c0_depth r1_level) (normalization_5962 c0_depth r1_level)))))

theorem normalization_5964 (c0_depth c0_kind c0_sign r1_level : Int) : (¬ (formula_1658 c0_depth c0_kind c0_sign r1_level)) ↔ (¬ (shared_expr_Classification051_19 c0_depth c0_kind c0_sign r1_level)) := (not_congr (normalization_5963 c0_depth c0_kind c0_sign r1_level))

abbrev shared_expr_Classification051_20 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification051_19 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))))
theorem normalization_5965 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (formula_1659 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Classification051_20 c0_depth c0_kind c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_5964 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_3540 c0_kind)))

theorem normalization_5966 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (¬ (formula_1659 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification051_20 c0_depth c0_kind c0_sign r1_group r1_level)) := (not_congr (normalization_5965 c0_depth c0_kind c0_sign r1_group r1_level))

theorem normalization_5967 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (formula_1659 c0_depth c0_kind c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification051_20 c0_depth c0_kind c0_sign r1_group r1_level))) := (or_congr (normalization_59 r1_mode) (or_congr (normalization_60 r1_mode) (normalization_5966 c0_depth c0_kind c0_sign r1_group r1_level)))

theorem normalization_5968 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (formula_1659 c0_depth c0_kind c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification051_20 c0_depth c0_kind c0_sign r1_group r1_level)))) := (not_congr (normalization_5967 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

theorem normalization_5969 (r1_mode : Int) : (r1_mode ≤ (1 : Int)) ↔ ((r1_mode) ≤ (1 : Int)) := by
  omega

theorem normalization_5970 (r1_mode : Int) : (¬ (r1_mode ≤ (1 : Int))) ↔ (¬ ((r1_mode) ≤ (1 : Int))) := (not_congr (normalization_5969 r1_mode))

theorem normalization_5971 (r1_mode : Int) : (r1_mode ≥ (1 : Int)) ↔ (¬ ((r1_mode) ≤ (0 : Int))) := by
  omega

theorem normalization_5972 (r1_mode : Int) : (¬ (r1_mode ≥ (1 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) := (not_congr (normalization_5971 r1_mode))

abbrev shared_expr_Classification051_21 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_5973 (c0_depth c0_kind c0_sign r1_level : Int) : (formula_1660 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Classification051_21 c0_depth c0_kind c0_sign r1_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5496 c0_sign) (or_congr (normalization_5960 c0_depth r1_level) (normalization_5962 c0_depth r1_level)))))

theorem normalization_5974 (c0_depth c0_kind c0_sign r1_level : Int) : (¬ (formula_1660 c0_depth c0_kind c0_sign r1_level)) ↔ (¬ (shared_expr_Classification051_21 c0_depth c0_kind c0_sign r1_level)) := (not_congr (normalization_5973 c0_depth c0_kind c0_sign r1_level))

abbrev shared_expr_Classification051_22 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification051_21 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))))
theorem normalization_5975 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (formula_1661 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Classification051_22 c0_depth c0_kind c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_5974 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_3540 c0_kind)))

theorem normalization_5976 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (¬ (formula_1661 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification051_22 c0_depth c0_kind c0_sign r1_group r1_level)) := (not_congr (normalization_5975 c0_depth c0_kind c0_sign r1_group r1_level))

theorem normalization_5977 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_1661 c0_depth c0_kind c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification051_22 c0_depth c0_kind c0_sign r1_group r1_level))) := (or_congr (normalization_5970 r1_mode) (or_congr (normalization_5972 r1_mode) (normalization_5976 c0_depth c0_kind c0_sign r1_group r1_level)))

theorem normalization_5978 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_1661 c0_depth c0_kind c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification051_22 c0_depth c0_kind c0_sign r1_group r1_level)))) := (not_congr (normalization_5977 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

theorem normalization_5979 (r1_mode : Int) : (r1_mode ≤ (2 : Int)) ↔ ((r1_mode) ≤ (2 : Int)) := by
  omega

theorem normalization_5980 (r1_mode : Int) : (¬ (r1_mode ≤ (2 : Int))) ↔ (¬ ((r1_mode) ≤ (2 : Int))) := (not_congr (normalization_5979 r1_mode))

theorem normalization_5981 (r1_mode : Int) : (r1_mode ≥ (2 : Int)) ↔ (¬ ((r1_mode) ≤ (1 : Int))) := by
  omega

theorem normalization_5982 (r1_mode : Int) : (¬ (r1_mode ≥ (2 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) := (not_congr (normalization_5981 r1_mode))

theorem normalization_5983 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5984 (c0_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_5983 c0_depth r1_level))

theorem normalization_5985 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5986 (c0_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5985 c0_depth r1_level))

abbrev shared_expr_Classification051_23 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_5987 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_1662 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Classification051_23 c0_depth c0_kind c0_node c0_sign r1_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5484 c0_sign) (or_congr (normalization_5504 c0_node) (or_congr (normalization_5984 c0_depth r1_level) (normalization_5986 c0_depth r1_level))))))

theorem normalization_5988 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (¬ (formula_1662 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ (¬ (shared_expr_Classification051_23 c0_depth c0_kind c0_node c0_sign r1_level)) := (not_congr (normalization_5987 c0_depth c0_kind c0_node c0_sign r1_level))

abbrev shared_expr_Classification051_24 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification051_23 c0_depth c0_kind c0_node c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification051_19 c0_depth c0_kind c0_sign r1_level))))
theorem normalization_5989 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_1663 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Classification051_24 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_5988 c0_depth c0_kind c0_node c0_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_5964 c0_depth c0_kind c0_sign r1_level)))

theorem normalization_5990 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (¬ (formula_1663 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification051_24 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (not_congr (normalization_5989 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

theorem normalization_5991 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_1663 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification051_24 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := (or_congr (normalization_5980 r1_mode) (or_congr (normalization_5982 r1_mode) (normalization_5990 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))

theorem normalization_5992 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_1663 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification051_24 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) := (not_congr (normalization_5991 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

theorem normalization_5993 (r1_mode : Int) : (r1_mode ≤ (3 : Int)) ↔ ((r1_mode) ≤ (3 : Int)) := by
  omega

theorem normalization_5994 (r1_mode : Int) : (¬ (r1_mode ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int))) := (not_congr (normalization_5993 r1_mode))

theorem normalization_5995 (r1_mode : Int) : (r1_mode ≥ (3 : Int)) ↔ (¬ ((r1_mode) ≤ (2 : Int))) := by
  omega

theorem normalization_5996 (r1_mode : Int) : (¬ (r1_mode ≥ (3 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) := (not_congr (normalization_5995 r1_mode))

abbrev shared_expr_Classification051_25 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_5997 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_1664 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Classification051_25 c0_depth c0_kind c0_node c0_sign r1_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5484 c0_sign) (or_congr (normalization_5516 c0_node) (or_congr (normalization_5984 c0_depth r1_level) (normalization_5986 c0_depth r1_level))))))

theorem normalization_5998 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (¬ (formula_1664 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ (¬ (shared_expr_Classification051_25 c0_depth c0_kind c0_node c0_sign r1_level)) := (not_congr (normalization_5997 c0_depth c0_kind c0_node c0_sign r1_level))

abbrev shared_expr_Classification051_26 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification051_25 c0_depth c0_kind c0_node c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification051_19 c0_depth c0_kind c0_sign r1_level))))
theorem normalization_5999 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_1665 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Classification051_26 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_5998 c0_depth c0_kind c0_node c0_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_5964 c0_depth c0_kind c0_sign r1_level)))

theorem normalization_6000 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (¬ (formula_1665 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification051_26 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (not_congr (normalization_5999 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

theorem normalization_6001 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_1665 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification051_26 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := (or_congr (normalization_5994 r1_mode) (or_congr (normalization_5996 r1_mode) (normalization_6000 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))

theorem normalization_6002 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_1665 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification051_26 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) := (not_congr (normalization_6001 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

theorem normalization_6003 (r1_mode : Int) : (r1_mode ≤ (4 : Int)) ↔ ((r1_mode) ≤ (4 : Int)) := by
  omega

theorem normalization_6004 (r1_mode : Int) : (¬ (r1_mode ≤ (4 : Int))) ↔ (¬ ((r1_mode) ≤ (4 : Int))) := (not_congr (normalization_6003 r1_mode))

theorem normalization_6005 (r1_mode : Int) : (¬ (r1_mode ≥ (4 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) := (not_congr (normalization_134 r1_mode))

abbrev shared_expr_Classification051_27 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_6006 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_1666 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Classification051_27 c0_depth c0_kind c0_node c0_sign r1_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5496 c0_sign) (or_congr (normalization_5504 c0_node) (or_congr (normalization_5984 c0_depth r1_level) (normalization_5986 c0_depth r1_level))))))

theorem normalization_6007 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (¬ (formula_1666 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ (¬ (shared_expr_Classification051_27 c0_depth c0_kind c0_node c0_sign r1_level)) := (not_congr (normalization_6006 c0_depth c0_kind c0_node c0_sign r1_level))

abbrev shared_expr_Classification051_28 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification051_21 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification051_27 c0_depth c0_kind c0_node c0_sign r1_level))))
theorem normalization_6008 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_1667 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Classification051_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_5974 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_6007 c0_depth c0_kind c0_node c0_sign r1_level)))

theorem normalization_6009 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (¬ (formula_1667 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification051_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (not_congr (normalization_6008 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

theorem normalization_6010 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_1667 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification051_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := (or_congr (normalization_6004 r1_mode) (or_congr (normalization_6005 r1_mode) (normalization_6009 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))

theorem normalization_6011 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_1667 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification051_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) := (not_congr (normalization_6010 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

theorem normalization_6012 (r1_mode : Int) : (r1_mode ≤ (5 : Int)) ↔ ((r1_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_6013 (r1_mode : Int) : (¬ (r1_mode ≤ (5 : Int))) ↔ (¬ ((r1_mode) ≤ (5 : Int))) := (not_congr (normalization_6012 r1_mode))

theorem normalization_6014 (r1_mode : Int) : (r1_mode ≥ (5 : Int)) ↔ (¬ ((r1_mode) ≤ (4 : Int))) := by
  omega

theorem normalization_6015 (r1_mode : Int) : (¬ (r1_mode ≥ (5 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (4 : Int)))) := (not_congr (normalization_6014 r1_mode))

abbrev shared_expr_Classification051_29 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_6016 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (formula_1668 c0_depth c0_kind c0_node c0_sign r1_level) ↔ (shared_expr_Classification051_29 c0_depth c0_kind c0_node c0_sign r1_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5496 c0_sign) (or_congr (normalization_5516 c0_node) (or_congr (normalization_5984 c0_depth r1_level) (normalization_5986 c0_depth r1_level))))))

theorem normalization_6017 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : (¬ (formula_1668 c0_depth c0_kind c0_node c0_sign r1_level)) ↔ (¬ (shared_expr_Classification051_29 c0_depth c0_kind c0_node c0_sign r1_level)) := (not_congr (normalization_6016 c0_depth c0_kind c0_node c0_sign r1_level))

abbrev shared_expr_Classification051_30 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification051_21 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification051_29 c0_depth c0_kind c0_node c0_sign r1_level))))
theorem normalization_6018 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (formula_1669 c0_depth c0_kind c0_node c0_sign r1_group r1_level) ↔ (shared_expr_Classification051_30 c0_depth c0_kind c0_node c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_88 r1_group) (normalization_5974 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_88 r1_group)) (normalization_6017 c0_depth c0_kind c0_node c0_sign r1_level)))

theorem normalization_6019 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : (¬ (formula_1669 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Classification051_30 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) := (not_congr (normalization_6018 c0_depth c0_kind c0_node c0_sign r1_group r1_level))

theorem normalization_6020 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_1669 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification051_30 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := (or_congr (normalization_6013 r1_mode) (or_congr (normalization_6015 r1_mode) (normalization_6019 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))

theorem normalization_6021 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_1669 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification051_30 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) := (not_congr (normalization_6020 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

abbrev shared_expr_Classification051_31 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification051_20 c0_depth c0_kind c0_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification051_22 c0_depth c0_kind c0_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification051_24 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification051_26 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification051_28 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ∨ (¬ ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification051_30 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
theorem normalization_6022 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1670 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := (or_congr (normalization_5968 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (or_congr (normalization_5978 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (or_congr (normalization_5992 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (or_congr (normalization_6002 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (or_congr (normalization_6011 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_6021 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))))))

abbrev shared_expr_Classification051_32 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification051_33 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification051_32 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Classification051_34 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification051_35 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification051_34 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Classification051_36 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification051_37 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification051_32 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification051_36 c0_depth c0_kind c0_node c0_sign r1_level)))
abbrev shared_expr_Classification051_38 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification051_39 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification051_32 c0_depth c0_kind c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification051_38 c0_depth c0_kind c0_node c0_sign r1_level)))
abbrev shared_expr_Classification051_40 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification051_41 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification051_40 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification051_34 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Classification051_42 (c0_depth c0_kind c0_node c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification051_43 (c0_depth c0_kind c0_node c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification051_42 c0_depth c0_kind c0_node c0_sign r1_level)) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification051_34 c0_depth c0_kind c0_sign r1_level)))
abbrev shared_expr_Classification051_44 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification051_33 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification051_35 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification051_37 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (3 : Int)) ∧ (¬ ((r1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification051_39 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (4 : Int)) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification051_41 c0_depth c0_kind c0_node c0_sign r1_group r1_level)) ∨ ((((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification051_43 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))
theorem normalization_6023 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : ((formula_1726 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (formula_1670 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) ↔ ((shared_expr_Classification051_44 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) := (iff_congr (normalization_5868 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (normalization_6022 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))

abbrev shared_expr_Classification051_45 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode))) ∨ ((¬ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification051_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))
theorem normalization_6024 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1742 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_3515 c0_kind) (normalization_5956 c0_group c0_level c0_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_3515 c0_kind)) (normalization_6022 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))

abbrev shared_expr_Classification051_46 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification051_15 c0_group c0_level c0_mode r1_group r1_level r1_mode)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification051_44 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)))
abbrev shared_expr_Classification051_47 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((shared_expr_Classification051_46 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))
theorem normalization_6025 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1743 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_47 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_5869 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) (normalization_6024 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_2697 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1743 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_1417 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) (shared_expr_Classification051_15 c0_group c0_level c0_mode r1_group r1_level r1_mode) (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode) (shared_expr_Classification051_44 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (shared_expr_Classification051_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))
  have n0 : ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3517 c0_kind) (replay_1292 c0_kind)
  have n1 : ((shared_expr_Classification051_15 c0_group c0_level c0_mode r1_group r1_level r1_mode) ↔ (¬ (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode))) := by
    exact Iff.mp (normalization_5958 c0_group c0_level c0_mode r1_group r1_level r1_mode) (replay_2695 c0_group c0_level c0_mode r1_group r1_level r1_mode)
  have n2 : ((shared_expr_Classification051_44 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) := by
    exact Iff.mp (normalization_6023 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (replay_2696 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6025 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Classification051_48 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((formula_1742 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (formula_1671 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))
abbrev formula_1744 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification051_48 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_1418 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification051_49 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification051_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) ∨ ((¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode))))
theorem normalization_6026 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1671 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_3514 c0_kind) (normalization_6022 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_3514 c0_kind)) (normalization_5956 c0_group c0_level c0_mode r1_group r1_level r1_mode)))

abbrev shared_expr_Classification051_50 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((shared_expr_Classification051_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))
theorem normalization_6027 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1744 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_50 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_6024 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) (normalization_6026 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_2698 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1744 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_1418 ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) (shared_expr_Classification051_16 c0_group c0_level c0_mode r1_group r1_level r1_mode) (shared_expr_Classification051_31 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode))
  have hn := ht
  exact Iff.mpr (normalization_6027 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Classification051_51 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((formula_1727 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (formula_1671 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))
abbrev formula_1745 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification051_51 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)

theorem normalized_1419 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification051_52 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((shared_expr_Classification051_46 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))
theorem normalization_6028 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1745 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Classification051_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_5869 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) (normalization_6026 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_2699 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1745 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_1419 (shared_expr_Classification051_46 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) (shared_expr_Classification051_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) (shared_expr_Classification051_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode))
  have n0 : (shared_expr_Classification051_47 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_6025 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) (replay_2697 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Classification051_50 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_6027 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) (replay_2698 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6028 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) hn

-- Checked replay of rewrite.
theorem replay_2700 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : ((formula_1730 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) ↔ (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) := by
  classical
  first
  | (simp only [formula_1730, shared_expr_Classification050_146, formula_1728, shared_expr_Classification050_144, formula_1729, shared_expr_Classification050_145, formula_1704, shared_expr_Classification050_46, formula_1705, shared_expr_Classification050_47, formula_1706, shared_expr_Classification050_48, formula_1707, shared_expr_Classification050_49, formula_134, formula_122, formula_120, formula_121, formula_125, formula_123, formula_124, formula_127, formula_126, formula_129, formula_128, formula_131, formula_130, formula_133, formula_132, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_1420 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6029 (c0_depth r1_depth : Int) : (r1_depth ≤ c0_depth) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6030 (c0_depth r1_depth : Int) : (r1_depth ≥ c0_depth) ↔ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6031 (c0_depth r1_depth : Int) : ((r1_depth ≤ c0_depth) ∧ (r1_depth ≥ c0_depth)) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (and_congr (normalization_6029 c0_depth r1_depth) (normalization_6030 c0_depth r1_depth))

abbrev shared_expr_Classification051_53 (c0_depth r1_depth : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
theorem normalization_6032 (c0_depth r1_depth : Int) : ((r1_depth = c0_depth) ↔ ((r1_depth ≤ c0_depth) ∧ (r1_depth ≥ c0_depth))) ↔ (shared_expr_Classification051_53 c0_depth r1_depth) := (iff_congr (normalization_5765 c0_depth r1_depth) (normalization_6031 c0_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_2701 (c0_depth r1_depth : Int) : ((r1_depth = c0_depth) ↔ ((r1_depth ≤ c0_depth) ∧ (r1_depth ≥ c0_depth))) := by
  classical
  have ht := (normalized_1420 ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6032 c0_depth r1_depth) hn

theorem normalized_1421 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6033 (c0_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6034 (c0_depth r1_depth : Int) : ((r1_depth ≤ c0_depth) ↔ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_6029 c0_depth r1_depth) (normalization_6033 c0_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_2702 (c0_depth r1_depth : Int) : ((r1_depth ≤ c0_depth) ↔ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1421 ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6034 c0_depth r1_depth) hn

theorem normalized_1422 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6035 (c0_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6036 (c0_depth r1_depth : Int) : ((r1_depth ≥ c0_depth) ↔ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (iff_congr (normalization_6030 c0_depth r1_depth) (normalization_6035 c0_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_2703 (c0_depth r1_depth : Int) : ((r1_depth ≥ c0_depth) ↔ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1422 ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6036 c0_depth r1_depth) hn

theorem normalized_1423 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6037 (c0_depth r1_depth : Int) : (((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (and_congr (normalization_6033 c0_depth r1_depth) (normalization_6035 c0_depth r1_depth))

theorem normalization_6038 (c0_depth r1_depth : Int) : (((r1_depth ≤ c0_depth) ∧ (r1_depth ≥ c0_depth)) ↔ (((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification051_53 c0_depth r1_depth) := (iff_congr (normalization_6031 c0_depth r1_depth) (normalization_6037 c0_depth r1_depth))

-- Checked replay of monotonicity.
theorem replay_2704 (c0_depth r1_depth : Int) : (((r1_depth ≤ c0_depth) ∧ (r1_depth ≥ c0_depth)) ↔ (((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1423 ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6034 c0_depth r1_depth) (replay_2702 c0_depth r1_depth)
  have n1 : (((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6036 c0_depth r1_depth) (replay_2703 c0_depth r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6038 c0_depth r1_depth) hn

abbrev shared_expr_Classification051_54 (c0_depth r1_depth : Int) : Prop := ((((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))))))
abbrev formula_1746 (c0_depth r1_depth : Int) : Prop := (shared_expr_Classification051_54 c0_depth r1_depth)

theorem normalized_1424 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6039 (c0_depth r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_6033 c0_depth r1_depth))

theorem normalization_6040 (c0_depth r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (not_congr (normalization_6035 c0_depth r1_depth))

theorem normalization_6041 (c0_depth r1_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := (or_congr (normalization_6039 c0_depth r1_depth) (normalization_6040 c0_depth r1_depth))

theorem normalization_6042 (c0_depth r1_depth : Int) : (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))) := (not_congr (normalization_6041 c0_depth r1_depth))

abbrev shared_expr_Classification051_55 (c0_depth r1_depth : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))))
theorem normalization_6043 (c0_depth r1_depth : Int) : (formula_1746 c0_depth r1_depth) ↔ (shared_expr_Classification051_55 c0_depth r1_depth) := (iff_congr (normalization_6037 c0_depth r1_depth) (normalization_6042 c0_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_2705 (c0_depth r1_depth : Int) : (formula_1746 c0_depth r1_depth) := by
  classical
  have ht := (normalized_1424 ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6043 c0_depth r1_depth) hn

theorem normalized_1425 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6044 (c0_depth r1_depth : Int) : (((r1_depth ≤ c0_depth) ∧ (r1_depth ≥ c0_depth)) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification051_55 c0_depth r1_depth) := (iff_congr (normalization_6031 c0_depth r1_depth) (normalization_6042 c0_depth r1_depth))

-- Checked replay of trans.
theorem replay_2706 (c0_depth r1_depth : Int) : (((r1_depth ≤ c0_depth) ∧ (r1_depth ≥ c0_depth)) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1425 ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (shared_expr_Classification051_55 c0_depth r1_depth))
  have n0 : (shared_expr_Classification051_53 c0_depth r1_depth) := by
    exact Iff.mp (normalization_6038 c0_depth r1_depth) (replay_2704 c0_depth r1_depth)
  have n1 : (shared_expr_Classification051_55 c0_depth r1_depth) := by
    exact Iff.mp (normalization_6043 c0_depth r1_depth) (replay_2705 c0_depth r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6044 c0_depth r1_depth) hn

theorem normalized_1426 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6045 (c0_depth r1_depth : Int) : ((r1_depth = c0_depth) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification051_55 c0_depth r1_depth) := (iff_congr (normalization_5765 c0_depth r1_depth) (normalization_6042 c0_depth r1_depth))

-- Checked replay of trans.
theorem replay_2707 (c0_depth r1_depth : Int) : ((r1_depth = c0_depth) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1426 ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (shared_expr_Classification051_55 c0_depth r1_depth))
  have n0 : (shared_expr_Classification051_53 c0_depth r1_depth) := by
    exact Iff.mp (normalization_6032 c0_depth r1_depth) (replay_2701 c0_depth r1_depth)
  have n1 : (shared_expr_Classification051_55 c0_depth r1_depth) := by
    exact Iff.mp (normalization_6044 c0_depth r1_depth) (replay_2706 c0_depth r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6045 c0_depth r1_depth) hn

end H4Formal.Generated.Classification
