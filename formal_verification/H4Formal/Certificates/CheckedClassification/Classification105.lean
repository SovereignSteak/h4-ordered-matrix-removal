import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification104

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_6812 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i437 : ((formula_2869 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) : (formula_2911 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := by
  exact Iff.mp (replay_6811 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (replay_6810 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i437)

theorem normalized_2410 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8615 (c3_mode r3_mode : Int) : (r3_mode ≤ c3_mode) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8616 (c3_mode r3_mode : Int) : (r3_mode ≥ c3_mode) ↔ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_8617 (c3_mode r3_mode : Int) : ((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_8615 c3_mode r3_mode) (normalization_8616 c3_mode r3_mode))

abbrev shared_expr_Classification105_0 (c3_mode r3_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
theorem normalization_8618 (c3_mode r3_mode : Int) : ((r3_mode = c3_mode) ↔ ((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode))) ↔ (shared_expr_Classification105_0 c3_mode r3_mode) := (iff_congr (normalization_8433 c3_mode r3_mode) (normalization_8617 c3_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_6813 (c3_mode r3_mode : Int) : ((r3_mode = c3_mode) ↔ ((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode))) := by
  classical
  have ht := (normalized_2410 ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8618 c3_mode r3_mode) hn

theorem normalized_2411 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8619 (c3_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8620 (c3_mode r3_mode : Int) : ((r3_mode ≤ c3_mode) ↔ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (iff_congr (normalization_8615 c3_mode r3_mode) (normalization_8619 c3_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_6814 (c3_mode r3_mode : Int) : ((r3_mode ≤ c3_mode) ↔ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2411 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8620 c3_mode r3_mode) hn

theorem normalized_2412 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8621 (c3_mode r3_mode : Int) : ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_8622 (c3_mode r3_mode : Int) : ((r3_mode ≥ c3_mode) ↔ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (iff_congr (normalization_8616 c3_mode r3_mode) (normalization_8621 c3_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_6815 (c3_mode r3_mode : Int) : ((r3_mode ≥ c3_mode) ↔ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2412 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8622 c3_mode r3_mode) hn

theorem normalized_2413 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8623 (c3_mode r3_mode : Int) : (((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (and_congr (normalization_8619 c3_mode r3_mode) (normalization_8621 c3_mode r3_mode))

theorem normalization_8624 (c3_mode r3_mode : Int) : (((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ (((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Classification105_0 c3_mode r3_mode) := (iff_congr (normalization_8617 c3_mode r3_mode) (normalization_8623 c3_mode r3_mode))

-- Checked replay of monotonicity.
theorem replay_6816 (c3_mode r3_mode : Int) : (((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ (((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2413 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8620 c3_mode r3_mode) (replay_6814 c3_mode r3_mode)
  have n1 : (((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ↔ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8622 c3_mode r3_mode) (replay_6815 c3_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8624 c3_mode r3_mode) hn

abbrev shared_expr_Classification105_1 (c3_mode r3_mode : Int) : Prop := ((((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))))
abbrev formula_2913 (c3_mode r3_mode : Int) : Prop := (shared_expr_Classification105_1 c3_mode r3_mode)

theorem normalized_2414 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8625 (c3_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_8619 c3_mode r3_mode))

theorem normalization_8626 (c3_mode r3_mode : Int) : (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) := (not_congr (normalization_8621 c3_mode r3_mode))

theorem normalization_8627 (c3_mode r3_mode : Int) : ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) := (or_congr (normalization_8625 c3_mode r3_mode) (normalization_8626 c3_mode r3_mode))

theorem normalization_8628 (c3_mode r3_mode : Int) : (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) := (not_congr (normalization_8627 c3_mode r3_mode))

abbrev shared_expr_Classification105_2 (c3_mode r3_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))))
theorem normalization_8629 (c3_mode r3_mode : Int) : (formula_2913 c3_mode r3_mode) ↔ (shared_expr_Classification105_2 c3_mode r3_mode) := (iff_congr (normalization_8623 c3_mode r3_mode) (normalization_8628 c3_mode r3_mode))

-- Checked replay of rewrite.
theorem replay_6817 (c3_mode r3_mode : Int) : (formula_2913 c3_mode r3_mode) := by
  classical
  have ht := (normalized_2414 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8629 c3_mode r3_mode) hn

theorem normalized_2415 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8630 (c3_mode r3_mode : Int) : (((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification105_2 c3_mode r3_mode) := (iff_congr (normalization_8617 c3_mode r3_mode) (normalization_8628 c3_mode r3_mode))

-- Checked replay of trans.
theorem replay_6818 (c3_mode r3_mode : Int) : (((r3_mode ≤ c3_mode) ∧ (r3_mode ≥ c3_mode)) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2415 ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Classification105_2 c3_mode r3_mode))
  have n0 : (shared_expr_Classification105_0 c3_mode r3_mode) := by
    exact Iff.mp (normalization_8624 c3_mode r3_mode) (replay_6816 c3_mode r3_mode)
  have n1 : (shared_expr_Classification105_2 c3_mode r3_mode) := by
    exact Iff.mp (normalization_8629 c3_mode r3_mode) (replay_6817 c3_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8630 c3_mode r3_mode) hn

theorem normalized_2416 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8631 (c3_mode r3_mode : Int) : ((r3_mode = c3_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification105_2 c3_mode r3_mode) := (iff_congr (normalization_8433 c3_mode r3_mode) (normalization_8628 c3_mode r3_mode))

-- Checked replay of trans.
theorem replay_6819 (c3_mode r3_mode : Int) : ((r3_mode = c3_mode) ↔ (¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2416 ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) (shared_expr_Classification105_2 c3_mode r3_mode))
  have n0 : (shared_expr_Classification105_0 c3_mode r3_mode) := by
    exact Iff.mp (normalization_8618 c3_mode r3_mode) (replay_6813 c3_mode r3_mode)
  have n1 : (shared_expr_Classification105_2 c3_mode r3_mode) := by
    exact Iff.mp (normalization_8630 c3_mode r3_mode) (replay_6818 c3_mode r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8631 c3_mode r3_mode) hn

theorem normalized_2417 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8632 (c3_level r3_level : Int) : (r3_level ≤ c3_level) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8633 (c3_level r3_level : Int) : (r3_level ≥ c3_level) ↔ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_8634 (c3_level r3_level : Int) : ((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_8632 c3_level r3_level) (normalization_8633 c3_level r3_level))

abbrev shared_expr_Classification105_3 (c3_level r3_level : Int) : Prop := (((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
theorem normalization_8635 (c3_level r3_level : Int) : ((r3_level = c3_level) ↔ ((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level))) ↔ (shared_expr_Classification105_3 c3_level r3_level) := (iff_congr (normalization_8434 c3_level r3_level) (normalization_8634 c3_level r3_level))

-- Checked replay of rewrite.
theorem replay_6820 (c3_level r3_level : Int) : ((r3_level = c3_level) ↔ ((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level))) := by
  classical
  have ht := (normalized_2417 ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8635 c3_level r3_level) hn

theorem normalized_2418 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8636 (c3_level r3_level : Int) : ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8637 (c3_level r3_level : Int) : ((r3_level ≤ c3_level) ↔ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_8632 c3_level r3_level) (normalization_8636 c3_level r3_level))

-- Checked replay of rewrite.
theorem replay_6821 (c3_level r3_level : Int) : ((r3_level ≤ c3_level) ↔ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2418 ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8637 c3_level r3_level) hn

theorem normalized_2419 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8638 (c3_level r3_level : Int) : ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_8639 (c3_level r3_level : Int) : ((r3_level ≥ c3_level) ↔ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (iff_congr (normalization_8633 c3_level r3_level) (normalization_8638 c3_level r3_level))

-- Checked replay of rewrite.
theorem replay_6822 (c3_level r3_level : Int) : ((r3_level ≥ c3_level) ↔ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2419 ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8639 c3_level r3_level) hn

theorem normalized_2420 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8640 (c3_level r3_level : Int) : (((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (and_congr (normalization_8636 c3_level r3_level) (normalization_8638 c3_level r3_level))

theorem normalization_8641 (c3_level r3_level : Int) : (((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ (((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ (shared_expr_Classification105_3 c3_level r3_level) := (iff_congr (normalization_8634 c3_level r3_level) (normalization_8640 c3_level r3_level))

-- Checked replay of monotonicity.
theorem replay_6823 (c3_level r3_level : Int) : (((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ (((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2420 ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8637 c3_level r3_level) (replay_6821 c3_level r3_level)
  have n1 : (((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ↔ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8639 c3_level r3_level) (replay_6822 c3_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8641 c3_level r3_level) hn

abbrev shared_expr_Classification105_4 (c3_level r3_level : Int) : Prop := ((((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))))
abbrev formula_2914 (c3_level r3_level : Int) : Prop := (shared_expr_Classification105_4 c3_level r3_level)

theorem normalized_2421 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8642 (c3_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_8636 c3_level r3_level))

theorem normalization_8643 (c3_level r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_8638 c3_level r3_level))

theorem normalization_8644 (c3_level r3_level : Int) : ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) := (or_congr (normalization_8642 c3_level r3_level) (normalization_8643 c3_level r3_level))

theorem normalization_8645 (c3_level r3_level : Int) : (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) := (not_congr (normalization_8644 c3_level r3_level))

abbrev shared_expr_Classification105_5 (c3_level r3_level : Int) : Prop := (((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))))
theorem normalization_8646 (c3_level r3_level : Int) : (formula_2914 c3_level r3_level) ↔ (shared_expr_Classification105_5 c3_level r3_level) := (iff_congr (normalization_8640 c3_level r3_level) (normalization_8645 c3_level r3_level))

-- Checked replay of rewrite.
theorem replay_6824 (c3_level r3_level : Int) : (formula_2914 c3_level r3_level) := by
  classical
  have ht := (normalized_2421 ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8646 c3_level r3_level) hn

theorem normalized_2422 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8647 (c3_level r3_level : Int) : (((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification105_5 c3_level r3_level) := (iff_congr (normalization_8634 c3_level r3_level) (normalization_8645 c3_level r3_level))

-- Checked replay of trans.
theorem replay_6825 (c3_level r3_level : Int) : (((r3_level ≤ c3_level) ∧ (r3_level ≥ c3_level)) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2422 ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Classification105_5 c3_level r3_level))
  have n0 : (shared_expr_Classification105_3 c3_level r3_level) := by
    exact Iff.mp (normalization_8641 c3_level r3_level) (replay_6823 c3_level r3_level)
  have n1 : (shared_expr_Classification105_5 c3_level r3_level) := by
    exact Iff.mp (normalization_8646 c3_level r3_level) (replay_6824 c3_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8647 c3_level r3_level) hn

theorem normalized_2423 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8648 (c3_level r3_level : Int) : ((r3_level = c3_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification105_5 c3_level r3_level) := (iff_congr (normalization_8434 c3_level r3_level) (normalization_8645 c3_level r3_level))

-- Checked replay of trans.
theorem replay_6826 (c3_level r3_level : Int) : ((r3_level = c3_level) ↔ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2423 ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) (shared_expr_Classification105_5 c3_level r3_level))
  have n0 : (shared_expr_Classification105_3 c3_level r3_level) := by
    exact Iff.mp (normalization_8635 c3_level r3_level) (replay_6820 c3_level r3_level)
  have n1 : (shared_expr_Classification105_5 c3_level r3_level) := by
    exact Iff.mp (normalization_8647 c3_level r3_level) (replay_6825 c3_level r3_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8648 c3_level r3_level) hn

theorem normalized_2424 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8649 (c3_group r3_group : Int) : (r3_group ≤ c3_group) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8650 (c3_group r3_group : Int) : (r3_group ≥ c3_group) ↔ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_8651 (c3_group r3_group : Int) : ((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_8649 c3_group r3_group) (normalization_8650 c3_group r3_group))

abbrev shared_expr_Classification105_6 (c3_group r3_group : Int) : Prop := (((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
theorem normalization_8652 (c3_group r3_group : Int) : ((r3_group = c3_group) ↔ ((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group))) ↔ (shared_expr_Classification105_6 c3_group r3_group) := (iff_congr (normalization_8504 c3_group r3_group) (normalization_8651 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6827 (c3_group r3_group : Int) : ((r3_group = c3_group) ↔ ((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group))) := by
  classical
  have ht := (normalized_2424 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8652 c3_group r3_group) hn

theorem normalized_2425 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8653 (c3_group r3_group : Int) : ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8654 (c3_group r3_group : Int) : ((r3_group ≤ c3_group) ↔ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_8649 c3_group r3_group) (normalization_8653 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6828 (c3_group r3_group : Int) : ((r3_group ≤ c3_group) ↔ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2425 ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8654 c3_group r3_group) hn

theorem normalized_2426 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8655 (c3_group r3_group : Int) : ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_8656 (c3_group r3_group : Int) : ((r3_group ≥ c3_group) ↔ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (iff_congr (normalization_8650 c3_group r3_group) (normalization_8655 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6829 (c3_group r3_group : Int) : ((r3_group ≥ c3_group) ↔ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2426 ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8656 c3_group r3_group) hn

theorem normalized_2427 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8657 (c3_group r3_group : Int) : (((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (and_congr (normalization_8653 c3_group r3_group) (normalization_8655 c3_group r3_group))

theorem normalization_8658 (c3_group r3_group : Int) : (((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ (((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ↔ (shared_expr_Classification105_6 c3_group r3_group) := (iff_congr (normalization_8651 c3_group r3_group) (normalization_8657 c3_group r3_group))

-- Checked replay of monotonicity.
theorem replay_6830 (c3_group r3_group : Int) : (((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ (((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2427 ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8654 c3_group r3_group) (replay_6828 c3_group r3_group)
  have n1 : (((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)) ↔ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8656 c3_group r3_group) (replay_6829 c3_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8658 c3_group r3_group) hn

abbrev shared_expr_Classification105_7 (c3_group r3_group : Int) : Prop := ((((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int)) ∧ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))
abbrev formula_2915 (c3_group r3_group : Int) : Prop := (shared_expr_Classification105_7 c3_group r3_group)

theorem normalized_2428 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8659 (c3_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_8653 c3_group r3_group))

theorem normalization_8660 (c3_group r3_group : Int) : (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) := (not_congr (normalization_8655 c3_group r3_group))

theorem normalization_8661 (c3_group r3_group : Int) : ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) := (or_congr (normalization_8659 c3_group r3_group) (normalization_8660 c3_group r3_group))

theorem normalization_8662 (c3_group r3_group : Int) : (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))) := (not_congr (normalization_8661 c3_group r3_group))

abbrev shared_expr_Classification105_8 (c3_group r3_group : Int) : Prop := (((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_8663 (c3_group r3_group : Int) : (formula_2915 c3_group r3_group) ↔ (shared_expr_Classification105_8 c3_group r3_group) := (iff_congr (normalization_8657 c3_group r3_group) (normalization_8662 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6831 (c3_group r3_group : Int) : (formula_2915 c3_group r3_group) := by
  classical
  have ht := (normalized_2428 ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)) ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8663 c3_group r3_group) hn

theorem normalized_2429 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8664 (c3_group r3_group : Int) : (((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification105_8 c3_group r3_group) := (iff_congr (normalization_8651 c3_group r3_group) (normalization_8662 c3_group r3_group))

-- Checked replay of trans.
theorem replay_6832 (c3_group r3_group : Int) : (((r3_group ≤ c3_group) ∧ (r3_group ≥ c3_group)) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2429 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Classification105_8 c3_group r3_group))
  have n0 : (shared_expr_Classification105_6 c3_group r3_group) := by
    exact Iff.mp (normalization_8658 c3_group r3_group) (replay_6830 c3_group r3_group)
  have n1 : (shared_expr_Classification105_8 c3_group r3_group) := by
    exact Iff.mp (normalization_8663 c3_group r3_group) (replay_6831 c3_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8664 c3_group r3_group) hn

theorem normalized_2430 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8665 (c3_group r3_group : Int) : ((r3_group = c3_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification105_8 c3_group r3_group) := (iff_congr (normalization_8504 c3_group r3_group) (normalization_8662 c3_group r3_group))

-- Checked replay of trans.
theorem replay_6833 (c3_group r3_group : Int) : ((r3_group = c3_group) ↔ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2430 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) (shared_expr_Classification105_8 c3_group r3_group))
  have n0 : (shared_expr_Classification105_6 c3_group r3_group) := by
    exact Iff.mp (normalization_8652 c3_group r3_group) (replay_6827 c3_group r3_group)
  have n1 : (shared_expr_Classification105_8 c3_group r3_group) := by
    exact Iff.mp (normalization_8664 c3_group r3_group) (replay_6832 c3_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8665 c3_group r3_group) hn

theorem normalized_2431 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8666 (c3_group r3_group : Int) : (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) := (not_congr (normalization_8662 c3_group r3_group))

abbrev shared_expr_Classification105_9 (c3_group r3_group : Int) : Prop := ((¬ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))))
theorem normalization_8667 (c3_group r3_group : Int) : ((¬ (r3_group = c3_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Classification105_9 c3_group r3_group) := (iff_congr (normalization_8505 c3_group r3_group) (normalization_8666 c3_group r3_group))

-- Checked replay of monotonicity.
theorem replay_6834 (c3_group r3_group : Int) : ((¬ (r3_group = c3_group)) ↔ (¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_2431 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification105_8 c3_group r3_group) := by
    exact Iff.mp (normalization_8665 c3_group r3_group) (replay_6833 c3_group r3_group)
  have hn := ht n0
  exact Iff.mpr (normalization_8667 c3_group r3_group) hn

abbrev shared_expr_Classification105_10 (c3_group r3_group : Int) : Prop := ((¬ (¬ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2916 (c3_group r3_group : Int) : Prop := (shared_expr_Classification105_10 c3_group r3_group)

theorem normalized_2432 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification105_11 (c3_group r3_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_8668 (c3_group r3_group : Int) : (formula_2916 c3_group r3_group) ↔ (shared_expr_Classification105_11 c3_group r3_group) := (iff_congr (normalization_8666 c3_group r3_group) (normalization_8661 c3_group r3_group))

-- Checked replay of rewrite.
theorem replay_6835 (c3_group r3_group : Int) : (formula_2916 c3_group r3_group) := by
  classical
  have ht := (normalized_2432 ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8668 c3_group r3_group) hn

theorem normalized_2433 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification105_12 (c3_group r3_group : Int) : Prop := ((¬ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_8669 (c3_group r3_group : Int) : ((¬ (r3_group = c3_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) ↔ (shared_expr_Classification105_12 c3_group r3_group) := (iff_congr (normalization_8505 c3_group r3_group) (normalization_8661 c3_group r3_group))

-- Checked replay of trans.
theorem replay_6836 (c3_group r3_group : Int) : ((¬ (r3_group = c3_group)) ↔ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_2433 ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification105_9 c3_group r3_group) := by
    exact Iff.mp (normalization_8667 c3_group r3_group) (replay_6834 c3_group r3_group)
  have n1 : (shared_expr_Classification105_11 c3_group r3_group) := by
    exact Iff.mp (normalization_8668 c3_group r3_group) (replay_6835 c3_group r3_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8669 c3_group r3_group) hn

abbrev shared_expr_Classification105_13 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((r3_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r3_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r3_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ∧ ((¬ ((r3_group + ((-1 : Int) * c3_group)) ≤ (0 : Int))) ∨ (¬ ((r3_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2917 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification105_13 c3_group c3_level c3_mode r3_group r3_level r3_mode)

theorem normalized_2434 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification105_14 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_8670 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (formula_2917 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_14 c3_group c3_level c3_mode r3_group r3_level r3_mode) := (and_congr (normalization_8628 c3_mode r3_mode) (and_congr (normalization_8645 c3_level r3_level) (normalization_8661 c3_group r3_group)))

abbrev shared_expr_Classification105_15 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := (((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∧ ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
theorem normalization_8671 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group))) ↔ (formula_2917 c3_group c3_level c3_mode r3_group r3_level r3_mode)) ↔ ((shared_expr_Classification105_15 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_14 c3_group c3_level c3_mode r3_group r3_level r3_mode)) := (iff_congr (normalization_8506 c3_group c3_level c3_mode r3_group r3_level r3_mode) (normalization_8670 c3_group c3_level c3_mode r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_6837 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group))) ↔ (formula_2917 c3_group c3_level c3_mode r3_group r3_level r3_mode)) := by
  classical
  have ht := (normalized_2434 ((¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int))) ∧ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)))) ((¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ((¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)))) ((¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int))) ∧ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))) ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification105_2 c3_mode r3_mode) := by
    exact Iff.mp (normalization_8631 c3_mode r3_mode) (replay_6819 c3_mode r3_mode)
  have n1 : (shared_expr_Classification105_5 c3_level r3_level) := by
    exact Iff.mp (normalization_8648 c3_level r3_level) (replay_6826 c3_level r3_level)
  have n2 : (shared_expr_Classification105_12 c3_group r3_group) := by
    exact Iff.mp (normalization_8669 c3_group r3_group) (replay_6836 c3_group r3_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8671 c3_group c3_level c3_mode r3_group r3_level r3_mode) hn

theorem normalized_2435 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification105_16 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : Prop := ((¬ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∨ (¬ ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int))))))
theorem normalization_8672 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (formula_2846 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode) := (or_congr (normalization_8625 c3_mode r3_mode) (or_congr (normalization_8626 c3_mode r3_mode) (or_congr (normalization_8642 c3_level r3_level) (or_congr (normalization_8643 c3_level r3_level) (normalization_8662 c3_group r3_group)))))

theorem normalization_8673 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (¬ (formula_2846 c3_group c3_level c3_mode r3_group r3_level r3_mode)) ↔ (¬ (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode)) := (not_congr (normalization_8672 c3_group c3_level c3_mode r3_group r3_level r3_mode))

theorem normalization_8674 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : ((formula_2917 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (formula_2846 c3_group c3_level c3_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Classification105_14 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_8670 c3_group c3_level c3_mode r3_group r3_level r3_mode) (normalization_8673 c3_group c3_level c3_mode r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_6838 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : ((formula_2917 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (formula_2846 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_2435 ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (-1 : Int)) ((c3_mode + ((-1 : Int) * r3_mode)) ≤ (0 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((c3_level + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ((¬ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (-1 : Int)))) ∨ (¬ ((c3_group + ((-1 : Int) * r3_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_8674 c3_group c3_level c3_mode r3_group r3_level r3_mode) hn

theorem normalized_2436 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8675 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group))) ↔ (¬ (formula_2846 c3_group c3_level c3_mode r3_group r3_level r3_mode))) ↔ ((shared_expr_Classification105_15 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := (iff_congr (normalization_8506 c3_group c3_level c3_mode r3_group r3_level r3_mode) (normalization_8673 c3_group c3_level c3_mode r3_group r3_level r3_mode))

-- Checked replay of trans.
theorem replay_6839 (c3_group c3_level c3_mode r3_group r3_level r3_mode : Int) : (((r3_mode = c3_mode) ∧ (r3_level = c3_level) ∧ (¬ (r3_group = c3_group))) ↔ (¬ (formula_2846 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := by
  classical
  have ht := (normalized_2436 (shared_expr_Classification105_15 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Classification105_14 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode))
  have n0 : ((shared_expr_Classification105_15 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_14 c3_group c3_level c3_mode r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_8671 c3_group c3_level c3_mode r3_group r3_level r3_mode) (replay_6837 c3_group c3_level c3_mode r3_group r3_level r3_mode)
  have n1 : ((shared_expr_Classification105_14 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_8674 c3_group c3_level c3_mode r3_group r3_level r3_mode) (replay_6838 c3_group c3_level c3_mode r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8675 c3_group c3_level c3_mode r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_6840 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((formula_2902 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (formula_2845 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) := by
  classical
  first
  | (simp only [formula_2902, shared_expr_Classification104_164, formula_2896, shared_expr_Classification104_158, formula_2897, shared_expr_Classification104_159, formula_2898, shared_expr_Classification104_160, formula_2899, shared_expr_Classification104_161, formula_2900, shared_expr_Classification104_162, formula_2901, shared_expr_Classification104_163, formula_2845, shared_expr_Classification104_33, formula_2834, shared_expr_Classification104_22, formula_2833, shared_expr_Classification104_21, formula_2836, shared_expr_Classification104_24, formula_2835, shared_expr_Classification104_23, formula_2838, shared_expr_Classification104_26, formula_2837, shared_expr_Classification104_25, formula_2840, shared_expr_Classification104_28, formula_2839, shared_expr_Classification104_27, formula_2842, shared_expr_Classification104_30, formula_2841, shared_expr_Classification104_29, formula_2844, shared_expr_Classification104_32, formula_2843, shared_expr_Classification104_31, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Classification105_17 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∧ (¬ (formula_2846 c3_group c3_level c3_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ∧ (formula_2845 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
abbrev formula_2918 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification105_17 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)

abbrev shared_expr_Classification105_18 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_2903 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (formula_2918 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
abbrev formula_2919 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification105_18 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)

theorem normalized_2437 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8676 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_8677 (c3_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) := (not_congr (normalization_8676 c3_depth r3_level))

theorem normalization_8678 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_8679 (c3_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := (not_congr (normalization_8678 c3_depth r3_level))

abbrev shared_expr_Classification105_19 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_8680 (c3_depth c3_kind c3_sign r3_level : Int) : (formula_2833 c3_depth c3_kind c3_sign r3_level) ↔ (shared_expr_Classification105_19 c3_depth c3_kind c3_sign r3_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6827 c3_sign) (or_congr (normalization_8677 c3_depth r3_level) (normalization_8679 c3_depth r3_level)))))

theorem normalization_8681 (c3_depth c3_kind c3_sign r3_level : Int) : (¬ (formula_2833 c3_depth c3_kind c3_sign r3_level)) ↔ (¬ (shared_expr_Classification105_19 c3_depth c3_kind c3_sign r3_level)) := (not_congr (normalization_8680 c3_depth c3_kind c3_sign r3_level))

abbrev shared_expr_Classification105_20 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification105_19 c3_depth c3_kind c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
theorem normalization_8682 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (formula_2834 c3_depth c3_kind c3_sign r3_group r3_level) ↔ (shared_expr_Classification105_20 c3_depth c3_kind c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_8681 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_6839 c3_kind)))

theorem normalization_8683 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (¬ (formula_2834 c3_depth c3_kind c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification105_20 c3_depth c3_kind c3_sign r3_group r3_level)) := (not_congr (normalization_8682 c3_depth c3_kind c3_sign r3_group r3_level))

theorem normalization_8684 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_2834 c3_depth c3_kind c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification105_20 c3_depth c3_kind c3_sign r3_group r3_level))) := (or_congr (normalization_2549 r3_mode) (or_congr (normalization_2551 r3_mode) (normalization_8683 c3_depth c3_kind c3_sign r3_group r3_level)))

theorem normalization_8685 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (formula_2834 c3_depth c3_kind c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification105_20 c3_depth c3_kind c3_sign r3_group r3_level)))) := (not_congr (normalization_8684 c3_depth c3_kind c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification105_21 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))))
theorem normalization_8686 (c3_depth c3_kind c3_sign r3_level : Int) : (formula_2835 c3_depth c3_kind c3_sign r3_level) ↔ (shared_expr_Classification105_21 c3_depth c3_kind c3_sign r3_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6851 c3_sign) (or_congr (normalization_8677 c3_depth r3_level) (normalization_8679 c3_depth r3_level)))))

theorem normalization_8687 (c3_depth c3_kind c3_sign r3_level : Int) : (¬ (formula_2835 c3_depth c3_kind c3_sign r3_level)) ↔ (¬ (shared_expr_Classification105_21 c3_depth c3_kind c3_sign r3_level)) := (not_congr (normalization_8686 c3_depth c3_kind c3_sign r3_level))

abbrev shared_expr_Classification105_22 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification105_21 c3_depth c3_kind c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (1 : Int))))))))
theorem normalization_8688 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (formula_2836 c3_depth c3_kind c3_sign r3_group r3_level) ↔ (shared_expr_Classification105_22 c3_depth c3_kind c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_8687 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_6839 c3_kind)))

theorem normalization_8689 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : (¬ (formula_2836 c3_depth c3_kind c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification105_22 c3_depth c3_kind c3_sign r3_group r3_level)) := (not_congr (normalization_8688 c3_depth c3_kind c3_sign r3_group r3_level))

theorem normalization_8690 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_2836 c3_depth c3_kind c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification105_22 c3_depth c3_kind c3_sign r3_group r3_level))) := (or_congr (normalization_2568 r3_mode) (or_congr (normalization_2570 r3_mode) (normalization_8689 c3_depth c3_kind c3_sign r3_group r3_level)))

theorem normalization_8691 (c3_depth c3_kind c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (1 : Int))) ∨ (¬ (r3_mode ≥ (1 : Int))) ∨ (¬ (formula_2836 c3_depth c3_kind c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification105_22 c3_depth c3_kind c3_sign r3_group r3_level)))) := (not_congr (normalization_8690 c3_depth c3_kind c3_sign r3_group r3_level r3_mode))

theorem normalization_8692 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_8693 (c3_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) := (not_congr (normalization_8692 c3_depth r3_level))

theorem normalization_8694 (c3_depth r3_level : Int) : ((r3_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8695 (c3_depth r3_level : Int) : (¬ ((r3_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_8694 c3_depth r3_level))

abbrev shared_expr_Classification105_23 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_8696 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (formula_2837 c3_depth c3_kind c3_node c3_sign r3_level) ↔ (shared_expr_Classification105_23 c3_depth c3_kind c3_node c3_sign r3_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6827 c3_sign) (or_congr (normalization_6859 c3_node) (or_congr (normalization_8693 c3_depth r3_level) (normalization_8695 c3_depth r3_level))))))

theorem normalization_8697 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (¬ (formula_2837 c3_depth c3_kind c3_node c3_sign r3_level)) ↔ (¬ (shared_expr_Classification105_23 c3_depth c3_kind c3_node c3_sign r3_level)) := (not_congr (normalization_8696 c3_depth c3_kind c3_node c3_sign r3_level))

abbrev shared_expr_Classification105_24 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification105_23 c3_depth c3_kind c3_node c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification105_19 c3_depth c3_kind c3_sign r3_level))))
theorem normalization_8698 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2838 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Classification105_24 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_8697 c3_depth c3_kind c3_node c3_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_8681 c3_depth c3_kind c3_sign r3_level)))

theorem normalization_8699 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (¬ (formula_2838 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification105_24 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (not_congr (normalization_8698 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

theorem normalization_8700 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_2838 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification105_24 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) := (or_congr (normalization_2578 r3_mode) (or_congr (normalization_2580 r3_mode) (normalization_8699 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))

theorem normalization_8701 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (2 : Int))) ∨ (¬ (r3_mode ≥ (2 : Int))) ∨ (¬ (formula_2838 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification105_24 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) := (not_congr (normalization_8700 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification105_25 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_8702 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (formula_2839 c3_depth c3_kind c3_node c3_sign r3_level) ↔ (shared_expr_Classification105_25 c3_depth c3_kind c3_node c3_sign r3_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6827 c3_sign) (or_congr (normalization_6871 c3_node) (or_congr (normalization_8693 c3_depth r3_level) (normalization_8695 c3_depth r3_level))))))

theorem normalization_8703 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (¬ (formula_2839 c3_depth c3_kind c3_node c3_sign r3_level)) ↔ (¬ (shared_expr_Classification105_25 c3_depth c3_kind c3_node c3_sign r3_level)) := (not_congr (normalization_8702 c3_depth c3_kind c3_node c3_sign r3_level))

abbrev shared_expr_Classification105_26 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification105_25 c3_depth c3_kind c3_node c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification105_19 c3_depth c3_kind c3_sign r3_level))))
theorem normalization_8704 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2840 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Classification105_26 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_8703 c3_depth c3_kind c3_node c3_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_8681 c3_depth c3_kind c3_sign r3_level)))

theorem normalization_8705 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (¬ (formula_2840 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification105_26 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (not_congr (normalization_8704 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

theorem normalization_8706 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_2840 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification105_26 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) := (or_congr (normalization_2592 r3_mode) (or_congr (normalization_2594 r3_mode) (normalization_8705 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))

theorem normalization_8707 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (3 : Int))) ∨ (¬ (r3_mode ≥ (3 : Int))) ∨ (¬ (formula_2840 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification105_26 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) := (not_congr (normalization_8706 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification105_27 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_8708 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (formula_2841 c3_depth c3_kind c3_node c3_sign r3_level) ↔ (shared_expr_Classification105_27 c3_depth c3_kind c3_node c3_sign r3_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6851 c3_sign) (or_congr (normalization_6859 c3_node) (or_congr (normalization_8693 c3_depth r3_level) (normalization_8695 c3_depth r3_level))))))

theorem normalization_8709 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (¬ (formula_2841 c3_depth c3_kind c3_node c3_sign r3_level)) ↔ (¬ (shared_expr_Classification105_27 c3_depth c3_kind c3_node c3_sign r3_level)) := (not_congr (normalization_8708 c3_depth c3_kind c3_node c3_sign r3_level))

abbrev shared_expr_Classification105_28 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification105_21 c3_depth c3_kind c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification105_27 c3_depth c3_kind c3_node c3_sign r3_level))))
theorem normalization_8710 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2842 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Classification105_28 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_8687 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_8709 c3_depth c3_kind c3_node c3_sign r3_level)))

theorem normalization_8711 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (¬ (formula_2842 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification105_28 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (not_congr (normalization_8710 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

theorem normalization_8712 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_2842 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification105_28 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) := (or_congr (normalization_2602 r3_mode) (or_congr (normalization_2603 r3_mode) (normalization_8711 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))

theorem normalization_8713 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (4 : Int))) ∨ (¬ (r3_mode ≥ (4 : Int))) ∨ (¬ (formula_2842 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification105_28 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) := (not_congr (normalization_8712 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification105_29 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c3_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))))
theorem normalization_8714 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (formula_2843 c3_depth c3_kind c3_node c3_sign r3_level) ↔ (shared_expr_Classification105_29 c3_depth c3_kind c3_node c3_sign r3_level) := (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6851 c3_sign) (or_congr (normalization_6871 c3_node) (or_congr (normalization_8693 c3_depth r3_level) (normalization_8695 c3_depth r3_level))))))

theorem normalization_8715 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : (¬ (formula_2843 c3_depth c3_kind c3_node c3_sign r3_level)) ↔ (¬ (shared_expr_Classification105_29 c3_depth c3_kind c3_node c3_sign r3_level)) := (not_congr (normalization_8714 c3_depth c3_kind c3_node c3_sign r3_level))

abbrev shared_expr_Classification105_30 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := ((((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification105_21 c3_depth c3_kind c3_sign r3_level))) ∨ ((¬ ((¬ ((r3_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification105_29 c3_depth c3_kind c3_node c3_sign r3_level))))
theorem normalization_8716 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (formula_2844 c3_depth c3_kind c3_node c3_sign r3_group r3_level) ↔ (shared_expr_Classification105_30 c3_depth c3_kind c3_node c3_sign r3_group r3_level) := (or_congr (and_congr (normalization_2556 r3_group) (normalization_8687 c3_depth c3_kind c3_sign r3_level)) (and_congr (not_congr (normalization_2556 r3_group)) (normalization_8715 c3_depth c3_kind c3_node c3_sign r3_level)))

theorem normalization_8717 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : (¬ (formula_2844 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ↔ (¬ (shared_expr_Classification105_30 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) := (not_congr (normalization_8716 c3_depth c3_kind c3_node c3_sign r3_group r3_level))

theorem normalization_8718 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_2844 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) ↔ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification105_30 c3_depth c3_kind c3_node c3_sign r3_group r3_level))) := (or_congr (normalization_2611 r3_mode) (or_congr (normalization_2613 r3_mode) (normalization_8717 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))

theorem normalization_8719 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (¬ ((¬ (r3_mode ≤ (5 : Int))) ∨ (¬ (r3_mode ≥ (5 : Int))) ∨ (¬ (formula_2844 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ↔ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification105_30 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) := (not_congr (normalization_8718 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification105_31 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((¬ ((¬ ((r3_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification105_20 c3_depth c3_kind c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification105_22 c3_depth c3_kind c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification105_24 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification105_26 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification105_28 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))) ∨ (¬ ((¬ ((r3_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r3_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification105_30 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))))
theorem normalization_8720 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2845 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_31 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) := (or_congr (normalization_8685 c3_depth c3_kind c3_sign r3_group r3_level r3_mode) (or_congr (normalization_8691 c3_depth c3_kind c3_sign r3_group r3_level r3_mode) (or_congr (normalization_8701 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (or_congr (normalization_8707 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (or_congr (normalization_8713 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (normalization_8719 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))))))

abbrev shared_expr_Classification105_32 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification105_33 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification105_32 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Classification105_34 (c3_depth c3_kind c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification105_35 (c3_depth c3_kind c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification105_34 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Classification105_36 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification105_37 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification105_32 c3_depth c3_kind c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification105_36 c3_depth c3_kind c3_node c3_sign r3_level)))
abbrev shared_expr_Classification105_38 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification105_39 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification105_32 c3_depth c3_kind c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification105_38 c3_depth c3_kind c3_node c3_sign r3_level)))
abbrev shared_expr_Classification105_40 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification105_41 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification105_40 c3_depth c3_kind c3_node c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification105_34 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Classification105_42 (c3_depth c3_kind c3_node c3_sign r3_level : Int) : Prop := ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ (((c3_depth + ((-1 : Int) * r3_level)) ≤ (0 : Int)) ∧ (¬ ((c3_depth + ((-1 : Int) * r3_level)) ≤ (-1 : Int)))) ∧ ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (((c3_sign) ≤ (2 : Int)) ∧ (¬ ((c3_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c3_node / (2 : Int))) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification105_43 (c3_depth c3_kind c3_node c3_sign r3_group r3_level : Int) : Prop := (((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification105_42 c3_depth c3_kind c3_node c3_sign r3_level)) ∨ ((¬ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification105_34 c3_depth c3_kind c3_sign r3_level)))
abbrev shared_expr_Classification105_44 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification105_33 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (1 : Int)) ∧ (¬ ((r3_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification105_35 c3_depth c3_kind c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (2 : Int)) ∧ (¬ ((r3_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification105_37 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (3 : Int)) ∧ (¬ ((r3_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification105_39 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (4 : Int)) ∧ (¬ ((r3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification105_41 c3_depth c3_kind c3_node c3_sign r3_group r3_level)) ∨ ((((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification105_43 c3_depth c3_kind c3_node c3_sign r3_group r3_level)))
theorem normalization_8721 (c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode : Int) : ((formula_2902 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (formula_2845 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) ↔ ((shared_expr_Classification105_44 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_31 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) := (iff_congr (normalization_8585 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (normalization_8720 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))

abbrev shared_expr_Classification105_45 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode))) ∨ ((¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification105_31 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
theorem normalization_8722 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2918 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_45 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_6746 c3_kind) (normalization_8673 c3_group c3_level c3_mode r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_6746 c3_kind)) (normalization_8720 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))

abbrev shared_expr_Classification105_46 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification105_15 c3_group c3_level c3_mode r3_group r3_level r3_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification105_44 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)))
abbrev shared_expr_Classification105_47 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification105_46 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_45 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
theorem normalization_8723 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2919 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_47 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := (iff_congr (normalization_8586 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) (normalization_8722 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))

-- Checked replay of monotonicity.
theorem replay_6841 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2919 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_2437 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification105_15 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Classification105_44 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (shared_expr_Classification105_31 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))
  have n0 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6748 c3_kind) (replay_4923 c3_kind)
  have n1 : ((shared_expr_Classification105_15 c3_group c3_level c3_mode r3_group r3_level r3_mode) ↔ (¬ (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode))) := by
    exact Iff.mp (normalization_8675 c3_group c3_level c3_mode r3_group r3_level r3_mode) (replay_6839 c3_group c3_level c3_mode r3_group r3_level r3_mode)
  have n2 : ((shared_expr_Classification105_44 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_31 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) := by
    exact Iff.mp (normalization_8721 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode) (replay_6840 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_8723 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) hn

abbrev shared_expr_Classification105_48 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_2918 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (formula_2847 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
abbrev formula_2920 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification105_48 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)

theorem normalized_2438 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification105_49 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification105_31 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) ∨ ((¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode))))
theorem normalization_8724 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2847 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_49 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := (or_congr (and_congr (normalization_6745 c3_kind) (normalization_8720 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode)) (and_congr (not_congr (normalization_6745 c3_kind)) (normalization_8673 c3_group c3_level c3_mode r3_group r3_level r3_mode)))

abbrev shared_expr_Classification105_50 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification105_45 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_49 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
theorem normalization_8725 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2920 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_50 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := (iff_congr (normalization_8722 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) (normalization_8724 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))

-- Checked replay of rewrite.
theorem replay_6842 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2920 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_2438 ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) (shared_expr_Classification105_16 c3_group c3_level c3_mode r3_group r3_level r3_mode) (shared_expr_Classification105_31 c3_depth c3_kind c3_node c3_sign r3_group r3_level r3_mode))
  have hn := ht
  exact Iff.mpr (normalization_8725 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) hn

abbrev shared_expr_Classification105_51 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((formula_2903 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (formula_2847 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
abbrev formula_2921 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := (shared_expr_Classification105_51 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)

theorem normalized_2439 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification105_52 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : Prop := ((shared_expr_Classification105_46 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_49 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
theorem normalization_8726 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2921 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) ↔ (shared_expr_Classification105_52 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := (iff_congr (normalization_8586 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) (normalization_8724 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))

-- Checked replay of trans.
theorem replay_6843 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode : Int) : (formula_2921 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := by
  classical
  have ht := (normalized_2439 (shared_expr_Classification105_46 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) (shared_expr_Classification105_45 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) (shared_expr_Classification105_49 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode))
  have n0 : (shared_expr_Classification105_47 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_8723 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) (replay_6841 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)
  have n1 : (shared_expr_Classification105_50 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) := by
    exact Iff.mp (normalization_8725 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) (replay_6842 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8726 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign r3_group r3_level r3_mode) hn

-- Checked replay of rewrite.
theorem replay_6844 (c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign : Int) : ((formula_2906 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign) ↔ (formula_2830 c3_group c3_level c3_mode r3_depth r3_kind r3_node r3_sign)) := by
  classical
  first
  | (simp only [formula_2906, shared_expr_Classification104_168, formula_2904, shared_expr_Classification104_166, formula_2905, shared_expr_Classification104_167, formula_2880, shared_expr_Classification104_68, formula_2881, shared_expr_Classification104_69, formula_2882, shared_expr_Classification104_70, formula_2883, shared_expr_Classification104_71, formula_2830, shared_expr_Classification104_18, formula_2818, shared_expr_Classification104_6, formula_2816, shared_expr_Classification104_4, formula_2817, shared_expr_Classification104_5, formula_2821, shared_expr_Classification104_9, formula_2819, shared_expr_Classification104_7, formula_2820, shared_expr_Classification104_8, formula_2823, shared_expr_Classification104_11, formula_2822, shared_expr_Classification104_10, formula_2825, shared_expr_Classification104_13, formula_2824, shared_expr_Classification104_12, formula_2827, shared_expr_Classification104_15, formula_2826, shared_expr_Classification104_14, formula_2829, shared_expr_Classification104_17, formula_2828, shared_expr_Classification104_16, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_2440 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8727 (c3_depth r3_depth : Int) : (r3_depth ≤ c3_depth) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8728 (c3_depth r3_depth : Int) : (r3_depth ≥ c3_depth) ↔ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_8729 (c3_depth r3_depth : Int) : ((r3_depth ≤ c3_depth) ∧ (r3_depth ≥ c3_depth)) ↔ ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (and_congr (normalization_8727 c3_depth r3_depth) (normalization_8728 c3_depth r3_depth))

abbrev shared_expr_Classification105_53 (c3_depth r3_depth : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
theorem normalization_8730 (c3_depth r3_depth : Int) : ((r3_depth = c3_depth) ↔ ((r3_depth ≤ c3_depth) ∧ (r3_depth ≥ c3_depth))) ↔ (shared_expr_Classification105_53 c3_depth r3_depth) := (iff_congr (normalization_8485 c3_depth r3_depth) (normalization_8729 c3_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_6845 (c3_depth r3_depth : Int) : ((r3_depth = c3_depth) ↔ ((r3_depth ≤ c3_depth) ∧ (r3_depth ≥ c3_depth))) := by
  classical
  have ht := (normalized_2440 ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_8730 c3_depth r3_depth) hn

theorem normalized_2441 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8731 (c3_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_8732 (c3_depth r3_depth : Int) : ((r3_depth ≤ c3_depth) ↔ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_8727 c3_depth r3_depth) (normalization_8731 c3_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_6846 (c3_depth r3_depth : Int) : ((r3_depth ≤ c3_depth) ↔ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2441 ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8732 c3_depth r3_depth) hn

theorem normalized_2442 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8733 (c3_depth r3_depth : Int) : ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_8734 (c3_depth r3_depth : Int) : ((r3_depth ≥ c3_depth) ↔ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (iff_congr (normalization_8728 c3_depth r3_depth) (normalization_8733 c3_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_6847 (c3_depth r3_depth : Int) : ((r3_depth ≥ c3_depth) ↔ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2442 ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8734 c3_depth r3_depth) hn

theorem normalized_2443 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8735 (c3_depth r3_depth : Int) : (((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (and_congr (normalization_8731 c3_depth r3_depth) (normalization_8733 c3_depth r3_depth))

theorem normalization_8736 (c3_depth r3_depth : Int) : (((r3_depth ≤ c3_depth) ∧ (r3_depth ≥ c3_depth)) ↔ (((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification105_53 c3_depth r3_depth) := (iff_congr (normalization_8729 c3_depth r3_depth) (normalization_8735 c3_depth r3_depth))

-- Checked replay of monotonicity.
theorem replay_6848 (c3_depth r3_depth : Int) : (((r3_depth ≤ c3_depth) ∧ (r3_depth ≥ c3_depth)) ↔ (((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2443 ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_8732 c3_depth r3_depth) (replay_6846 c3_depth r3_depth)
  have n1 : (((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ↔ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_8734 c3_depth r3_depth) (replay_6847 c3_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8736 c3_depth r3_depth) hn

abbrev shared_expr_Classification105_54 (c3_depth r3_depth : Int) : Prop := ((((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))))
abbrev formula_2922 (c3_depth r3_depth : Int) : Prop := (shared_expr_Classification105_54 c3_depth r3_depth)

theorem normalized_2444 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8737 (c3_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_8731 c3_depth r3_depth))

theorem normalization_8738 (c3_depth r3_depth : Int) : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := (not_congr (normalization_8733 c3_depth r3_depth))

theorem normalization_8739 (c3_depth r3_depth : Int) : ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := (or_congr (normalization_8737 c3_depth r3_depth) (normalization_8738 c3_depth r3_depth))

theorem normalization_8740 (c3_depth r3_depth : Int) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))) := (not_congr (normalization_8739 c3_depth r3_depth))

abbrev shared_expr_Classification105_55 (c3_depth r3_depth : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))))))
theorem normalization_8741 (c3_depth r3_depth : Int) : (formula_2922 c3_depth r3_depth) ↔ (shared_expr_Classification105_55 c3_depth r3_depth) := (iff_congr (normalization_8735 c3_depth r3_depth) (normalization_8740 c3_depth r3_depth))

-- Checked replay of rewrite.
theorem replay_6849 (c3_depth r3_depth : Int) : (formula_2922 c3_depth r3_depth) := by
  classical
  have ht := (normalized_2444 ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8741 c3_depth r3_depth) hn

theorem normalized_2445 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8742 (c3_depth r3_depth : Int) : (((r3_depth ≤ c3_depth) ∧ (r3_depth ≥ c3_depth)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification105_55 c3_depth r3_depth) := (iff_congr (normalization_8729 c3_depth r3_depth) (normalization_8740 c3_depth r3_depth))

-- Checked replay of trans.
theorem replay_6850 (c3_depth r3_depth : Int) : (((r3_depth ≤ c3_depth) ∧ (r3_depth ≥ c3_depth)) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2445 ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (shared_expr_Classification105_55 c3_depth r3_depth))
  have n0 : (shared_expr_Classification105_53 c3_depth r3_depth) := by
    exact Iff.mp (normalization_8736 c3_depth r3_depth) (replay_6848 c3_depth r3_depth)
  have n1 : (shared_expr_Classification105_55 c3_depth r3_depth) := by
    exact Iff.mp (normalization_8741 c3_depth r3_depth) (replay_6849 c3_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8742 c3_depth r3_depth) hn

theorem normalized_2446 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8743 (c3_depth r3_depth : Int) : ((r3_depth = c3_depth) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification105_55 c3_depth r3_depth) := (iff_congr (normalization_8485 c3_depth r3_depth) (normalization_8740 c3_depth r3_depth))

-- Checked replay of trans.
theorem replay_6851 (c3_depth r3_depth : Int) : ((r3_depth = c3_depth) ↔ (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2446 ((¬ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((c3_depth + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (shared_expr_Classification105_55 c3_depth r3_depth))
  have n0 : (shared_expr_Classification105_53 c3_depth r3_depth) := by
    exact Iff.mp (normalization_8730 c3_depth r3_depth) (replay_6845 c3_depth r3_depth)
  have n1 : (shared_expr_Classification105_55 c3_depth r3_depth) := by
    exact Iff.mp (normalization_8742 c3_depth r3_depth) (replay_6850 c3_depth r3_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8743 c3_depth r3_depth) hn

abbrev shared_expr_Classification105_56 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (((r3_sign = (0 : Int)) ∧ (c3_sign = (0 : Int)) ∧ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev formula_2923 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification105_56 c3_node c3_sign r3_node r3_sign)

theorem normalized_2447 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8744 (c3_node c3_sign r3_node r3_sign : Int) : ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (and_congr (normalization_622 r3_sign) (and_congr (normalization_6819 c3_sign) (normalization_8595 c3_node r3_node)))

abbrev shared_expr_Classification105_57 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ↔ ((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))
theorem normalization_8745 (c3_node c3_sign r3_node r3_sign : Int) : (formula_2923 c3_node c3_sign r3_node r3_sign) ↔ (shared_expr_Classification105_57 c3_node c3_sign r3_node r3_sign) := (iff_congr (normalization_8596 c3_node c3_sign r3_node r3_sign) (normalization_8744 c3_node c3_sign r3_node r3_sign))

-- Checked replay of monotonicity.
theorem replay_6852 (c3_node c3_sign r3_node r3_sign : Int) : (formula_2923 c3_node c3_sign r3_node r3_sign) := by
  classical
  have ht := (normalized_2447 (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))) (((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))) ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have n0 : ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_2651 r3_sign) (replay_976 r3_sign)
  have n1 : ((((c3_sign) ≤ (0 : Int)) ∧ (¬ ((c3_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6921 c3_sign) (replay_4968 c3_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_8745 c3_node c3_sign r3_node r3_sign) hn

abbrev shared_expr_Classification105_58 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∧ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))))
abbrev formula_2924 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification105_58 c3_node c3_sign r3_node r3_sign)

theorem normalized_2448 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_8746 (c3_node r3_node : Int) : (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_8595 c3_node r3_node))

theorem normalization_8747 (c3_node c3_sign r3_node r3_sign : Int) : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ↔ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int))))) := (or_congr (normalization_618 r3_sign) (or_congr (normalization_620 r3_sign) (or_congr (normalization_6815 c3_sign) (or_congr (normalization_6817 c3_sign) (normalization_8746 c3_node r3_node)))))

theorem normalization_8748 (c3_node c3_sign r3_node r3_sign : Int) : (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_8747 c3_node c3_sign r3_node r3_sign))

abbrev shared_expr_Classification105_59 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (((¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (¬ ((c3_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))))))
theorem normalization_8749 (c3_node c3_sign r3_node r3_sign : Int) : (formula_2924 c3_node c3_sign r3_node r3_sign) ↔ (shared_expr_Classification105_59 c3_node c3_sign r3_node r3_sign) := (iff_congr (normalization_8744 c3_node c3_sign r3_node r3_sign) (normalization_8748 c3_node c3_sign r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_6853 (c3_node c3_sign r3_node r3_sign : Int) : (formula_2924 c3_node c3_sign r3_node r3_sign) := by
  classical
  have ht := (normalized_2448 ((r3_sign) ≤ (0 : Int)) ((r3_sign) ≤ (-1 : Int)) ((c3_sign) ≤ (0 : Int)) ((c3_sign) ≤ (-1 : Int)) ((c3_node + ((-1 : Int) * r3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_8749 c3_node c3_sign r3_node r3_sign) hn

end H4Formal.Generated.Classification
