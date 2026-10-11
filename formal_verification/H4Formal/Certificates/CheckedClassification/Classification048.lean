import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification047

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_1308 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5430 (c0_mode r2_mode : Int) : (((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ ((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := (and_congr (normalization_5426 c0_mode r2_mode) (normalization_5428 c0_mode r2_mode))

abbrev shared_expr_Classification048_0 (c0_mode r2_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ↔ ((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))
theorem normalization_5431 (c0_mode r2_mode : Int) : (((r2_mode ≤ c0_mode) ∧ (r2_mode ≥ c0_mode)) ↔ (((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) ↔ (shared_expr_Classification048_0 c0_mode r2_mode) := (iff_congr (normalization_5424 c0_mode r2_mode) (normalization_5430 c0_mode r2_mode))

-- Checked replay of monotonicity.
theorem replay_2574 (c0_mode r2_mode : Int) : (((r2_mode ≤ c0_mode) ∧ (r2_mode ≥ c0_mode)) ↔ (((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1308 ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5427 c0_mode r2_mode) (replay_2572 c0_mode r2_mode)
  have n1 : (((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5429 c0_mode r2_mode) (replay_2573 c0_mode r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5431 c0_mode r2_mode) hn

abbrev shared_expr_Classification048_1 (c0_mode r2_mode : Int) : Prop := ((((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ∧ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))))
abbrev formula_1617 (c0_mode r2_mode : Int) : Prop := (shared_expr_Classification048_1 c0_mode r2_mode)

theorem normalized_1309 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5432 (c0_mode r2_mode : Int) : (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_5426 c0_mode r2_mode))

theorem normalization_5433 (c0_mode r2_mode : Int) : (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := (not_congr (normalization_5428 c0_mode r2_mode))

theorem normalization_5434 (c0_mode r2_mode : Int) : ((¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)))) := (or_congr (normalization_5432 c0_mode r2_mode) (normalization_5433 c0_mode r2_mode))

theorem normalization_5435 (c0_mode r2_mode : Int) : (¬ ((¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))) := (not_congr (normalization_5434 c0_mode r2_mode))

abbrev shared_expr_Classification048_2 (c0_mode r2_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))))
theorem normalization_5436 (c0_mode r2_mode : Int) : (formula_1617 c0_mode r2_mode) ↔ (shared_expr_Classification048_2 c0_mode r2_mode) := (iff_congr (normalization_5430 c0_mode r2_mode) (normalization_5435 c0_mode r2_mode))

-- Checked replay of rewrite.
theorem replay_2575 (c0_mode r2_mode : Int) : (formula_1617 c0_mode r2_mode) := by
  classical
  have ht := (normalized_1309 ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5436 c0_mode r2_mode) hn

theorem normalized_1310 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5437 (c0_mode r2_mode : Int) : (((r2_mode ≤ c0_mode) ∧ (r2_mode ≥ c0_mode)) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification048_2 c0_mode r2_mode) := (iff_congr (normalization_5424 c0_mode r2_mode) (normalization_5435 c0_mode r2_mode))

-- Checked replay of trans.
theorem replay_2576 (c0_mode r2_mode : Int) : (((r2_mode ≤ c0_mode) ∧ (r2_mode ≥ c0_mode)) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1310 ((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) (shared_expr_Classification048_2 c0_mode r2_mode))
  have n0 : (shared_expr_Classification048_0 c0_mode r2_mode) := by
    exact Iff.mp (normalization_5431 c0_mode r2_mode) (replay_2574 c0_mode r2_mode)
  have n1 : (shared_expr_Classification048_2 c0_mode r2_mode) := by
    exact Iff.mp (normalization_5436 c0_mode r2_mode) (replay_2575 c0_mode r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5437 c0_mode r2_mode) hn

theorem normalized_1311 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5438 (c0_mode r2_mode : Int) : ((r2_mode = c0_mode) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification048_2 c0_mode r2_mode) := (iff_congr (normalization_5240 c0_mode r2_mode) (normalization_5435 c0_mode r2_mode))

-- Checked replay of trans.
theorem replay_2577 (c0_mode r2_mode : Int) : ((r2_mode = c0_mode) ↔ (¬ ((¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1311 ((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) (shared_expr_Classification048_2 c0_mode r2_mode))
  have n0 : (shared_expr_Classification048_0 c0_mode r2_mode) := by
    exact Iff.mp (normalization_5425 c0_mode r2_mode) (replay_2571 c0_mode r2_mode)
  have n1 : (shared_expr_Classification048_2 c0_mode r2_mode) := by
    exact Iff.mp (normalization_5437 c0_mode r2_mode) (replay_2576 c0_mode r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5438 c0_mode r2_mode) hn

theorem normalized_1312 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5439 (c0_level r2_level : Int) : (r2_level ≤ c0_level) ↔ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5440 (c0_level r2_level : Int) : (r2_level ≥ c0_level) ↔ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5441 (c0_level r2_level : Int) : ((r2_level ≤ c0_level) ∧ (r2_level ≥ c0_level)) ↔ ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (and_congr (normalization_5439 c0_level r2_level) (normalization_5440 c0_level r2_level))

abbrev shared_expr_Classification048_3 (c0_level r2_level : Int) : Prop := (((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))
theorem normalization_5442 (c0_level r2_level : Int) : ((r2_level = c0_level) ↔ ((r2_level ≤ c0_level) ∧ (r2_level ≥ c0_level))) ↔ (shared_expr_Classification048_3 c0_level r2_level) := (iff_congr (normalization_5241 c0_level r2_level) (normalization_5441 c0_level r2_level))

-- Checked replay of rewrite.
theorem replay_2578 (c0_level r2_level : Int) : ((r2_level = c0_level) ↔ ((r2_level ≤ c0_level) ∧ (r2_level ≥ c0_level))) := by
  classical
  have ht := (normalized_1312 ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5442 c0_level r2_level) hn

theorem normalized_1313 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5443 (c0_level r2_level : Int) : ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ↔ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5444 (c0_level r2_level : Int) : ((r2_level ≤ c0_level) ↔ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_5439 c0_level r2_level) (normalization_5443 c0_level r2_level))

-- Checked replay of rewrite.
theorem replay_2579 (c0_level r2_level : Int) : ((r2_level ≤ c0_level) ↔ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1313 ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5444 c0_level r2_level) hn

theorem normalized_1314 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5445 (c0_level r2_level : Int) : ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5446 (c0_level r2_level : Int) : ((r2_level ≥ c0_level) ↔ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (iff_congr (normalization_5440 c0_level r2_level) (normalization_5445 c0_level r2_level))

-- Checked replay of rewrite.
theorem replay_2580 (c0_level r2_level : Int) : ((r2_level ≥ c0_level) ↔ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1314 ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5446 c0_level r2_level) hn

theorem normalized_1315 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5447 (c0_level r2_level : Int) : (((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (and_congr (normalization_5443 c0_level r2_level) (normalization_5445 c0_level r2_level))

theorem normalization_5448 (c0_level r2_level : Int) : (((r2_level ≤ c0_level) ∧ (r2_level ≥ c0_level)) ↔ (((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) ↔ (shared_expr_Classification048_3 c0_level r2_level) := (iff_congr (normalization_5441 c0_level r2_level) (normalization_5447 c0_level r2_level))

-- Checked replay of monotonicity.
theorem replay_2581 (c0_level r2_level : Int) : (((r2_level ≤ c0_level) ∧ (r2_level ≥ c0_level)) ↔ (((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1315 ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5444 c0_level r2_level) (replay_2579 c0_level r2_level)
  have n1 : (((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5446 c0_level r2_level) (replay_2580 c0_level r2_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5448 c0_level r2_level) hn

abbrev shared_expr_Classification048_4 (c0_level r2_level : Int) : Prop := ((((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ∧ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))))
abbrev formula_1618 (c0_level r2_level : Int) : Prop := (shared_expr_Classification048_4 c0_level r2_level)

theorem normalized_1316 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5449 (c0_level r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5443 c0_level r2_level))

theorem normalization_5450 (c0_level r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (not_congr (normalization_5445 c0_level r2_level))

theorem normalization_5451 (c0_level r2_level : Int) : ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)))) := (or_congr (normalization_5449 c0_level r2_level) (normalization_5450 c0_level r2_level))

theorem normalization_5452 (c0_level r2_level : Int) : (¬ ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))) := (not_congr (normalization_5451 c0_level r2_level))

abbrev shared_expr_Classification048_5 (c0_level r2_level : Int) : Prop := (((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))))
theorem normalization_5453 (c0_level r2_level : Int) : (formula_1618 c0_level r2_level) ↔ (shared_expr_Classification048_5 c0_level r2_level) := (iff_congr (normalization_5447 c0_level r2_level) (normalization_5452 c0_level r2_level))

-- Checked replay of rewrite.
theorem replay_2582 (c0_level r2_level : Int) : (formula_1618 c0_level r2_level) := by
  classical
  have ht := (normalized_1316 ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5453 c0_level r2_level) hn

theorem normalized_1317 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5454 (c0_level r2_level : Int) : (((r2_level ≤ c0_level) ∧ (r2_level ≥ c0_level)) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification048_5 c0_level r2_level) := (iff_congr (normalization_5441 c0_level r2_level) (normalization_5452 c0_level r2_level))

-- Checked replay of trans.
theorem replay_2583 (c0_level r2_level : Int) : (((r2_level ≤ c0_level) ∧ (r2_level ≥ c0_level)) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1317 ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) (shared_expr_Classification048_5 c0_level r2_level))
  have n0 : (shared_expr_Classification048_3 c0_level r2_level) := by
    exact Iff.mp (normalization_5448 c0_level r2_level) (replay_2581 c0_level r2_level)
  have n1 : (shared_expr_Classification048_5 c0_level r2_level) := by
    exact Iff.mp (normalization_5453 c0_level r2_level) (replay_2582 c0_level r2_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5454 c0_level r2_level) hn

theorem normalized_1318 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5455 (c0_level r2_level : Int) : ((r2_level = c0_level) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification048_5 c0_level r2_level) := (iff_congr (normalization_5241 c0_level r2_level) (normalization_5452 c0_level r2_level))

-- Checked replay of trans.
theorem replay_2584 (c0_level r2_level : Int) : ((r2_level = c0_level) ↔ (¬ ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1318 ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) (shared_expr_Classification048_5 c0_level r2_level))
  have n0 : (shared_expr_Classification048_3 c0_level r2_level) := by
    exact Iff.mp (normalization_5442 c0_level r2_level) (replay_2578 c0_level r2_level)
  have n1 : (shared_expr_Classification048_5 c0_level r2_level) := by
    exact Iff.mp (normalization_5454 c0_level r2_level) (replay_2583 c0_level r2_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5455 c0_level r2_level) hn

theorem normalized_1319 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5456 (c0_group r2_group : Int) : (r2_group ≤ c0_group) ↔ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5457 (c0_group r2_group : Int) : (r2_group ≥ c0_group) ↔ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_5458 (c0_group r2_group : Int) : ((r2_group ≤ c0_group) ∧ (r2_group ≥ c0_group)) ↔ ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := (and_congr (normalization_5456 c0_group r2_group) (normalization_5457 c0_group r2_group))

abbrev shared_expr_Classification048_6 (c0_group r2_group : Int) : Prop := (((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))
theorem normalization_5459 (c0_group r2_group : Int) : ((r2_group = c0_group) ↔ ((r2_group ≤ c0_group) ∧ (r2_group ≥ c0_group))) ↔ (shared_expr_Classification048_6 c0_group r2_group) := (iff_congr (normalization_5311 c0_group r2_group) (normalization_5458 c0_group r2_group))

-- Checked replay of rewrite.
theorem replay_2585 (c0_group r2_group : Int) : ((r2_group = c0_group) ↔ ((r2_group ≤ c0_group) ∧ (r2_group ≥ c0_group))) := by
  classical
  have ht := (normalized_1319 ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5459 c0_group r2_group) hn

theorem normalized_1320 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5460 (c0_group r2_group : Int) : ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ↔ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5461 (c0_group r2_group : Int) : ((r2_group ≤ c0_group) ↔ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := (iff_congr (normalization_5456 c0_group r2_group) (normalization_5460 c0_group r2_group))

-- Checked replay of rewrite.
theorem replay_2586 (c0_group r2_group : Int) : ((r2_group ≤ c0_group) ↔ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1320 ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5461 c0_group r2_group) hn

theorem normalized_1321 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5462 (c0_group r2_group : Int) : ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) := by
  omega

theorem normalization_5463 (c0_group r2_group : Int) : ((r2_group ≥ c0_group) ↔ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := (iff_congr (normalization_5457 c0_group r2_group) (normalization_5462 c0_group r2_group))

-- Checked replay of rewrite.
theorem replay_2587 (c0_group r2_group : Int) : ((r2_group ≥ c0_group) ↔ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1321 ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5463 c0_group r2_group) hn

theorem normalized_1322 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5464 (c0_group r2_group : Int) : (((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := (and_congr (normalization_5460 c0_group r2_group) (normalization_5462 c0_group r2_group))

theorem normalization_5465 (c0_group r2_group : Int) : (((r2_group ≤ c0_group) ∧ (r2_group ≥ c0_group)) ↔ (((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) ↔ (shared_expr_Classification048_6 c0_group r2_group) := (iff_congr (normalization_5458 c0_group r2_group) (normalization_5464 c0_group r2_group))

-- Checked replay of monotonicity.
theorem replay_2588 (c0_group r2_group : Int) : (((r2_group ≤ c0_group) ∧ (r2_group ≥ c0_group)) ↔ (((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1322 ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5461 c0_group r2_group) (replay_2586 c0_group r2_group)
  have n1 : (((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)) ↔ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5463 c0_group r2_group) (replay_2587 c0_group r2_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5465 c0_group r2_group) hn

abbrev shared_expr_Classification048_7 (c0_group r2_group : Int) : Prop := ((((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ∧ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))
abbrev formula_1619 (c0_group r2_group : Int) : Prop := (shared_expr_Classification048_7 c0_group r2_group)

theorem normalized_1323 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5466 (c0_group r2_group : Int) : (¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := (not_congr (normalization_5460 c0_group r2_group))

theorem normalization_5467 (c0_group r2_group : Int) : (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) ↔ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) := (not_congr (normalization_5462 c0_group r2_group))

theorem normalization_5468 (c0_group r2_group : Int) : ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))) := (or_congr (normalization_5466 c0_group r2_group) (normalization_5467 c0_group r2_group))

theorem normalization_5469 (c0_group r2_group : Int) : (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))) := (not_congr (normalization_5468 c0_group r2_group))

abbrev shared_expr_Classification048_8 (c0_group r2_group : Int) : Prop := (((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))))
theorem normalization_5470 (c0_group r2_group : Int) : (formula_1619 c0_group r2_group) ↔ (shared_expr_Classification048_8 c0_group r2_group) := (iff_congr (normalization_5464 c0_group r2_group) (normalization_5469 c0_group r2_group))

-- Checked replay of rewrite.
theorem replay_2589 (c0_group r2_group : Int) : (formula_1619 c0_group r2_group) := by
  classical
  have ht := (normalized_1323 ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5470 c0_group r2_group) hn

theorem normalized_1324 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5471 (c0_group r2_group : Int) : (((r2_group ≤ c0_group) ∧ (r2_group ≥ c0_group)) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification048_8 c0_group r2_group) := (iff_congr (normalization_5458 c0_group r2_group) (normalization_5469 c0_group r2_group))

-- Checked replay of trans.
theorem replay_2590 (c0_group r2_group : Int) : (((r2_group ≤ c0_group) ∧ (r2_group ≥ c0_group)) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1324 ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) (shared_expr_Classification048_8 c0_group r2_group))
  have n0 : (shared_expr_Classification048_6 c0_group r2_group) := by
    exact Iff.mp (normalization_5465 c0_group r2_group) (replay_2588 c0_group r2_group)
  have n1 : (shared_expr_Classification048_8 c0_group r2_group) := by
    exact Iff.mp (normalization_5470 c0_group r2_group) (replay_2589 c0_group r2_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5471 c0_group r2_group) hn

theorem normalized_1325 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5472 (c0_group r2_group : Int) : ((r2_group = c0_group) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification048_8 c0_group r2_group) := (iff_congr (normalization_5311 c0_group r2_group) (normalization_5469 c0_group r2_group))

-- Checked replay of trans.
theorem replay_2591 (c0_group r2_group : Int) : ((r2_group = c0_group) ↔ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1325 ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) (shared_expr_Classification048_8 c0_group r2_group))
  have n0 : (shared_expr_Classification048_6 c0_group r2_group) := by
    exact Iff.mp (normalization_5459 c0_group r2_group) (replay_2585 c0_group r2_group)
  have n1 : (shared_expr_Classification048_8 c0_group r2_group) := by
    exact Iff.mp (normalization_5471 c0_group r2_group) (replay_2590 c0_group r2_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5472 c0_group r2_group) hn

theorem normalized_1326 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5473 (c0_group r2_group : Int) : (¬ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))) := (not_congr (normalization_5469 c0_group r2_group))

abbrev shared_expr_Classification048_9 (c0_group r2_group : Int) : Prop := ((¬ ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))) ↔ (¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))))
theorem normalization_5474 (c0_group r2_group : Int) : ((¬ (r2_group = c0_group)) ↔ (¬ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))) ↔ (shared_expr_Classification048_9 c0_group r2_group) := (iff_congr (normalization_5312 c0_group r2_group) (normalization_5473 c0_group r2_group))

-- Checked replay of monotonicity.
theorem replay_2592 (c0_group r2_group : Int) : ((¬ (r2_group = c0_group)) ↔ (¬ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1326 ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification048_8 c0_group r2_group) := by
    exact Iff.mp (normalization_5472 c0_group r2_group) (replay_2591 c0_group r2_group)
  have hn := ht n0
  exact Iff.mpr (normalization_5474 c0_group r2_group) hn

abbrev shared_expr_Classification048_10 (c0_group r2_group : Int) : Prop := ((¬ (¬ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))) ↔ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))
abbrev formula_1620 (c0_group r2_group : Int) : Prop := (shared_expr_Classification048_10 c0_group r2_group)

theorem normalized_1327 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification048_11 (c0_group r2_group : Int) : Prop := ((¬ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
theorem normalization_5475 (c0_group r2_group : Int) : (formula_1620 c0_group r2_group) ↔ (shared_expr_Classification048_11 c0_group r2_group) := (iff_congr (normalization_5473 c0_group r2_group) (normalization_5468 c0_group r2_group))

-- Checked replay of rewrite.
theorem replay_2593 (c0_group r2_group : Int) : (formula_1620 c0_group r2_group) := by
  classical
  have ht := (normalized_1327 ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5475 c0_group r2_group) hn

theorem normalized_1328 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification048_12 (c0_group r2_group : Int) : Prop := ((¬ ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
theorem normalization_5476 (c0_group r2_group : Int) : ((¬ (r2_group = c0_group)) ↔ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) ↔ (shared_expr_Classification048_12 c0_group r2_group) := (iff_congr (normalization_5312 c0_group r2_group) (normalization_5468 c0_group r2_group))

-- Checked replay of trans.
theorem replay_2594 (c0_group r2_group : Int) : ((¬ (r2_group = c0_group)) ↔ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1328 ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification048_9 c0_group r2_group) := by
    exact Iff.mp (normalization_5474 c0_group r2_group) (replay_2592 c0_group r2_group)
  have n1 : (shared_expr_Classification048_11 c0_group r2_group) := by
    exact Iff.mp (normalization_5475 c0_group r2_group) (replay_2593 c0_group r2_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5476 c0_group r2_group) hn

abbrev shared_expr_Classification048_13 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))))) ∧ ((¬ ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))))
abbrev formula_1621 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification048_13 c0_group c0_level c0_mode r2_group r2_level r2_mode)

theorem normalized_1329 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ ((¬ p4) ↔ p5)) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification048_14 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))))) ∧ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
theorem normalization_5477 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : (formula_1621 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_14 c0_group c0_level c0_mode r2_group r2_level r2_mode) := (and_congr (normalization_5435 c0_mode r2_mode) (and_congr (normalization_5452 c0_level r2_level) (normalization_5468 c0_group r2_group)))

abbrev shared_expr_Classification048_15 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∧ ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
theorem normalization_5478 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : (((r2_mode = c0_mode) ∧ (r2_level = c0_level) ∧ (¬ (r2_group = c0_group))) ↔ (formula_1621 c0_group c0_level c0_mode r2_group r2_level r2_mode)) ↔ ((shared_expr_Classification048_15 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_14 c0_group c0_level c0_mode r2_group r2_level r2_mode)) := (iff_congr (normalization_5313 c0_group c0_level c0_mode r2_group r2_level r2_mode) (normalization_5477 c0_group c0_level c0_mode r2_group r2_level r2_mode))

-- Checked replay of monotonicity.
theorem replay_2595 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : (((r2_mode = c0_mode) ∧ (r2_level = c0_level) ∧ (¬ (r2_group = c0_group))) ↔ (formula_1621 c0_group c0_level c0_mode r2_group r2_level r2_mode)) := by
  classical
  have ht := (normalized_1329 ((¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ((¬ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)))) ((¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ((¬ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)))) ((¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) ∧ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))) ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have n0 : (shared_expr_Classification048_2 c0_mode r2_mode) := by
    exact Iff.mp (normalization_5438 c0_mode r2_mode) (replay_2577 c0_mode r2_mode)
  have n1 : (shared_expr_Classification048_5 c0_level r2_level) := by
    exact Iff.mp (normalization_5455 c0_level r2_level) (replay_2584 c0_level r2_level)
  have n2 : (shared_expr_Classification048_12 c0_group r2_group) := by
    exact Iff.mp (normalization_5476 c0_group r2_group) (replay_2594 c0_group r2_group)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5478 c0_group c0_level c0_mode r2_group r2_level r2_mode) hn

theorem normalized_1330 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification048_16 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int))))))
theorem normalization_5479 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : (formula_1550 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode) := (or_congr (normalization_5432 c0_mode r2_mode) (or_congr (normalization_5433 c0_mode r2_mode) (or_congr (normalization_5449 c0_level r2_level) (or_congr (normalization_5450 c0_level r2_level) (normalization_5469 c0_group r2_group)))))

theorem normalization_5480 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : (¬ (formula_1550 c0_group c0_level c0_mode r2_group r2_level r2_mode)) ↔ (¬ (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode)) := (not_congr (normalization_5479 c0_group c0_level c0_mode r2_group r2_level r2_mode))

theorem normalization_5481 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : ((formula_1621 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (¬ (formula_1550 c0_group c0_level c0_mode r2_group r2_level r2_mode))) ↔ ((shared_expr_Classification048_14 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (¬ (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode))) := (iff_congr (normalization_5477 c0_group c0_level c0_mode r2_group r2_level r2_mode) (normalization_5480 c0_group c0_level c0_mode r2_group r2_level r2_mode))

-- Checked replay of rewrite.
theorem replay_2596 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : ((formula_1621 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (¬ (formula_1550 c0_group c0_level c0_mode r2_group r2_level r2_mode))) := by
  classical
  have ht := (normalized_1330 ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) ((c0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((¬ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) ∨ (¬ ((c0_group + ((-1 : Int) * r2_group)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5481 c0_group c0_level c0_mode r2_group r2_level r2_mode) hn

theorem normalized_1331 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5482 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : (((r2_mode = c0_mode) ∧ (r2_level = c0_level) ∧ (¬ (r2_group = c0_group))) ↔ (¬ (formula_1550 c0_group c0_level c0_mode r2_group r2_level r2_mode))) ↔ ((shared_expr_Classification048_15 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (¬ (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode))) := (iff_congr (normalization_5313 c0_group c0_level c0_mode r2_group r2_level r2_mode) (normalization_5480 c0_group c0_level c0_mode r2_group r2_level r2_mode))

-- Checked replay of trans.
theorem replay_2597 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : (((r2_mode = c0_mode) ∧ (r2_level = c0_level) ∧ (¬ (r2_group = c0_group))) ↔ (¬ (formula_1550 c0_group c0_level c0_mode r2_group r2_level r2_mode))) := by
  classical
  have ht := (normalized_1331 (shared_expr_Classification048_15 c0_group c0_level c0_mode r2_group r2_level r2_mode) (shared_expr_Classification048_14 c0_group c0_level c0_mode r2_group r2_level r2_mode) (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode))
  have n0 : ((shared_expr_Classification048_15 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_14 c0_group c0_level c0_mode r2_group r2_level r2_mode)) := by
    exact Iff.mp (normalization_5478 c0_group c0_level c0_mode r2_group r2_level r2_mode) (replay_2595 c0_group c0_level c0_mode r2_group r2_level r2_mode)
  have n1 : ((shared_expr_Classification048_14 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (¬ (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode))) := by
    exact Iff.mp (normalization_5481 c0_group c0_level c0_mode r2_group r2_level r2_mode) (replay_2596 c0_group c0_level c0_mode r2_group r2_level r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5482 c0_group c0_level c0_mode r2_group r2_level r2_mode) hn

-- Checked replay of rewrite.
theorem replay_2598 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : ((formula_1606 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) ↔ (formula_1549 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)) := by
  classical
  first
  | (simp only [formula_1606, shared_expr_Classification047_126, formula_1600, shared_expr_Classification047_120, formula_1601, shared_expr_Classification047_121, formula_1602, shared_expr_Classification047_122, formula_1603, shared_expr_Classification047_123, formula_1604, shared_expr_Classification047_124, formula_1605, shared_expr_Classification047_125, formula_1549, shared_expr_Classification046_54, formula_1538, shared_expr_Classification046_43, formula_1537, shared_expr_Classification046_42, formula_1540, shared_expr_Classification046_45, formula_1539, shared_expr_Classification046_44, formula_1542, shared_expr_Classification046_47, formula_1541, shared_expr_Classification046_46, formula_1544, shared_expr_Classification046_49, formula_1543, shared_expr_Classification046_48, formula_1546, shared_expr_Classification046_51, formula_1545, shared_expr_Classification046_50, formula_1548, shared_expr_Classification046_53, formula_1547, shared_expr_Classification046_52, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

abbrev shared_expr_Classification048_17 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := (((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∧ (¬ (formula_1550 c0_group c0_level c0_mode r2_group r2_level r2_mode))) ∨ ((¬ (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) ∧ (formula_1549 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)))
abbrev formula_1622 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification048_17 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)

abbrev shared_expr_Classification048_18 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := ((formula_1607 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (formula_1622 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))
abbrev formula_1623 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification048_18 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)

theorem normalized_1332 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5483 (c0_sign : Int) : ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) := (or_congr (normalization_3582 c0_sign) (normalization_5233 c0_sign))

theorem normalization_5484 (c0_sign : Int) : (¬ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_5483 c0_sign))

theorem normalization_5485 (c0_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_5486 (c0_depth r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) := (not_congr (normalization_5485 c0_depth r2_level))

theorem normalization_5487 (c0_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5488 (c0_depth r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := (not_congr (normalization_5487 c0_depth r2_level))

abbrev shared_expr_Classification048_19 (c0_depth c0_kind c0_sign r2_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))
theorem normalization_5489 (c0_depth c0_kind c0_sign r2_level : Int) : (formula_1537 c0_depth c0_kind c0_sign r2_level) ↔ (shared_expr_Classification048_19 c0_depth c0_kind c0_sign r2_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5484 c0_sign) (or_congr (normalization_5486 c0_depth r2_level) (normalization_5488 c0_depth r2_level)))))

theorem normalization_5490 (c0_depth c0_kind c0_sign r2_level : Int) : (¬ (formula_1537 c0_depth c0_kind c0_sign r2_level)) ↔ (¬ (shared_expr_Classification048_19 c0_depth c0_kind c0_sign r2_level)) := (not_congr (normalization_5489 c0_depth c0_kind c0_sign r2_level))

abbrev shared_expr_Classification048_20 (c0_depth c0_kind c0_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification048_19 c0_depth c0_kind c0_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))))
theorem normalization_5491 (c0_depth c0_kind c0_sign r2_group r2_level : Int) : (formula_1538 c0_depth c0_kind c0_sign r2_group r2_level) ↔ (shared_expr_Classification048_20 c0_depth c0_kind c0_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_5490 c0_depth c0_kind c0_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_3540 c0_kind)))

theorem normalization_5492 (c0_depth c0_kind c0_sign r2_group r2_level : Int) : (¬ (formula_1538 c0_depth c0_kind c0_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification048_20 c0_depth c0_kind c0_sign r2_group r2_level)) := (not_congr (normalization_5491 c0_depth c0_kind c0_sign r2_group r2_level))

theorem normalization_5493 (c0_depth c0_kind c0_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1538 c0_depth c0_kind c0_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification048_20 c0_depth c0_kind c0_sign r2_group r2_level))) := (or_congr (normalization_388 r2_mode) (or_congr (normalization_389 r2_mode) (normalization_5492 c0_depth c0_kind c0_sign r2_group r2_level)))

theorem normalization_5494 (c0_depth c0_kind c0_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1538 c0_depth c0_kind c0_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification048_20 c0_depth c0_kind c0_sign r2_group r2_level)))) := (not_congr (normalization_5493 c0_depth c0_kind c0_sign r2_group r2_level r2_mode))

theorem normalization_5495 (c0_sign : Int) : ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) := (or_congr (normalization_5226 c0_sign) (normalization_5233 c0_sign))

theorem normalization_5496 (c0_sign : Int) : (¬ ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_5495 c0_sign))

abbrev shared_expr_Classification048_21 (c0_depth c0_kind c0_sign r2_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))
theorem normalization_5497 (c0_depth c0_kind c0_sign r2_level : Int) : (formula_1539 c0_depth c0_kind c0_sign r2_level) ↔ (shared_expr_Classification048_21 c0_depth c0_kind c0_sign r2_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5496 c0_sign) (or_congr (normalization_5486 c0_depth r2_level) (normalization_5488 c0_depth r2_level)))))

theorem normalization_5498 (c0_depth c0_kind c0_sign r2_level : Int) : (¬ (formula_1539 c0_depth c0_kind c0_sign r2_level)) ↔ (¬ (shared_expr_Classification048_21 c0_depth c0_kind c0_sign r2_level)) := (not_congr (normalization_5497 c0_depth c0_kind c0_sign r2_level))

abbrev shared_expr_Classification048_22 (c0_depth c0_kind c0_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification048_21 c0_depth c0_kind c0_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))))
theorem normalization_5499 (c0_depth c0_kind c0_sign r2_group r2_level : Int) : (formula_1540 c0_depth c0_kind c0_sign r2_group r2_level) ↔ (shared_expr_Classification048_22 c0_depth c0_kind c0_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_5498 c0_depth c0_kind c0_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_3540 c0_kind)))

theorem normalization_5500 (c0_depth c0_kind c0_sign r2_group r2_level : Int) : (¬ (formula_1540 c0_depth c0_kind c0_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification048_22 c0_depth c0_kind c0_sign r2_group r2_level)) := (not_congr (normalization_5499 c0_depth c0_kind c0_sign r2_group r2_level))

theorem normalization_5501 (c0_depth c0_kind c0_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1540 c0_depth c0_kind c0_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification048_22 c0_depth c0_kind c0_sign r2_group r2_level))) := (or_congr (normalization_4215 r2_mode) (or_congr (normalization_4217 r2_mode) (normalization_5500 c0_depth c0_kind c0_sign r2_group r2_level)))

theorem normalization_5502 (c0_depth c0_kind c0_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1540 c0_depth c0_kind c0_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification048_22 c0_depth c0_kind c0_sign r2_group r2_level)))) := (not_congr (normalization_5501 c0_depth c0_kind c0_sign r2_group r2_level r2_mode))

theorem normalization_5503 (c0_node : Int) : ((c0_node % (2 : Int)) ≤ (0 : Int)) ↔ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5504 (c0_node : Int) : (¬ ((c0_node % (2 : Int)) ≤ (0 : Int))) ↔ (¬ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5503 c0_node))

theorem normalization_5505 (c0_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_5506 (c0_depth r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := (not_congr (normalization_5505 c0_depth r2_level))

theorem normalization_5507 (c0_depth r2_level : Int) : ((r2_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5508 (c0_depth r2_level : Int) : (¬ ((r2_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5507 c0_depth r2_level))

abbrev shared_expr_Classification048_23 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
theorem normalization_5509 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : (formula_1541 c0_depth c0_kind c0_node c0_sign r2_level) ↔ (shared_expr_Classification048_23 c0_depth c0_kind c0_node c0_sign r2_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5484 c0_sign) (or_congr (normalization_5504 c0_node) (or_congr (normalization_5506 c0_depth r2_level) (normalization_5508 c0_depth r2_level))))))

theorem normalization_5510 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : (¬ (formula_1541 c0_depth c0_kind c0_node c0_sign r2_level)) ↔ (¬ (shared_expr_Classification048_23 c0_depth c0_kind c0_node c0_sign r2_level)) := (not_congr (normalization_5509 c0_depth c0_kind c0_node c0_sign r2_level))

abbrev shared_expr_Classification048_24 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification048_23 c0_depth c0_kind c0_node c0_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification048_19 c0_depth c0_kind c0_sign r2_level))))
theorem normalization_5511 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : (formula_1542 c0_depth c0_kind c0_node c0_sign r2_group r2_level) ↔ (shared_expr_Classification048_24 c0_depth c0_kind c0_node c0_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_5510 c0_depth c0_kind c0_node c0_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_5490 c0_depth c0_kind c0_sign r2_level)))

theorem normalization_5512 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : (¬ (formula_1542 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification048_24 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) := (not_congr (normalization_5511 c0_depth c0_kind c0_node c0_sign r2_group r2_level))

theorem normalization_5513 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1542 c0_depth c0_kind c0_node c0_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification048_24 c0_depth c0_kind c0_node c0_sign r2_group r2_level))) := (or_congr (normalization_4225 r2_mode) (or_congr (normalization_4227 r2_mode) (normalization_5512 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))

theorem normalization_5514 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1542 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification048_24 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) := (not_congr (normalization_5513 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode))

theorem normalization_5515 (c0_node : Int) : ((c0_node % (2 : Int)) ≥ (1 : Int)) ↔ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5516 (c0_node : Int) : (¬ ((c0_node % (2 : Int)) ≥ (1 : Int))) ↔ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := (not_congr (normalization_5515 c0_node))

abbrev shared_expr_Classification048_25 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
theorem normalization_5517 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : (formula_1543 c0_depth c0_kind c0_node c0_sign r2_level) ↔ (shared_expr_Classification048_25 c0_depth c0_kind c0_node c0_sign r2_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5484 c0_sign) (or_congr (normalization_5516 c0_node) (or_congr (normalization_5506 c0_depth r2_level) (normalization_5508 c0_depth r2_level))))))

theorem normalization_5518 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : (¬ (formula_1543 c0_depth c0_kind c0_node c0_sign r2_level)) ↔ (¬ (shared_expr_Classification048_25 c0_depth c0_kind c0_node c0_sign r2_level)) := (not_congr (normalization_5517 c0_depth c0_kind c0_node c0_sign r2_level))

abbrev shared_expr_Classification048_26 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification048_25 c0_depth c0_kind c0_node c0_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification048_19 c0_depth c0_kind c0_sign r2_level))))
theorem normalization_5519 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : (formula_1544 c0_depth c0_kind c0_node c0_sign r2_group r2_level) ↔ (shared_expr_Classification048_26 c0_depth c0_kind c0_node c0_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_5518 c0_depth c0_kind c0_node c0_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_5490 c0_depth c0_kind c0_sign r2_level)))

theorem normalization_5520 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : (¬ (formula_1544 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification048_26 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) := (not_congr (normalization_5519 c0_depth c0_kind c0_node c0_sign r2_group r2_level))

theorem normalization_5521 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1544 c0_depth c0_kind c0_node c0_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification048_26 c0_depth c0_kind c0_node c0_sign r2_group r2_level))) := (or_congr (normalization_4239 r2_mode) (or_congr (normalization_4241 r2_mode) (normalization_5520 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))

theorem normalization_5522 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1544 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification048_26 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) := (not_congr (normalization_5521 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode))

abbrev shared_expr_Classification048_27 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
theorem normalization_5523 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : (formula_1545 c0_depth c0_kind c0_node c0_sign r2_level) ↔ (shared_expr_Classification048_27 c0_depth c0_kind c0_node c0_sign r2_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5496 c0_sign) (or_congr (normalization_5504 c0_node) (or_congr (normalization_5506 c0_depth r2_level) (normalization_5508 c0_depth r2_level))))))

theorem normalization_5524 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : (¬ (formula_1545 c0_depth c0_kind c0_node c0_sign r2_level)) ↔ (¬ (shared_expr_Classification048_27 c0_depth c0_kind c0_node c0_sign r2_level)) := (not_congr (normalization_5523 c0_depth c0_kind c0_node c0_sign r2_level))

abbrev shared_expr_Classification048_28 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification048_21 c0_depth c0_kind c0_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification048_27 c0_depth c0_kind c0_node c0_sign r2_level))))
theorem normalization_5525 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : (formula_1546 c0_depth c0_kind c0_node c0_sign r2_group r2_level) ↔ (shared_expr_Classification048_28 c0_depth c0_kind c0_node c0_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_5498 c0_depth c0_kind c0_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_5524 c0_depth c0_kind c0_node c0_sign r2_level)))

theorem normalization_5526 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : (¬ (formula_1546 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification048_28 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) := (not_congr (normalization_5525 c0_depth c0_kind c0_node c0_sign r2_group r2_level))

theorem normalization_5527 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1546 c0_depth c0_kind c0_node c0_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification048_28 c0_depth c0_kind c0_node c0_sign r2_group r2_level))) := (or_congr (normalization_4249 r2_mode) (or_congr (normalization_4250 r2_mode) (normalization_5526 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))

theorem normalization_5528 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1546 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification048_28 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) := (not_congr (normalization_5527 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode))

abbrev shared_expr_Classification048_29 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))
theorem normalization_5529 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : (formula_1547 c0_depth c0_kind c0_node c0_sign r2_level) ↔ (shared_expr_Classification048_29 c0_depth c0_kind c0_node c0_sign r2_level) := (or_congr (normalization_5210 c0_kind) (or_congr (normalization_5212 c0_kind) (or_congr (normalization_5496 c0_sign) (or_congr (normalization_5516 c0_node) (or_congr (normalization_5506 c0_depth r2_level) (normalization_5508 c0_depth r2_level))))))

theorem normalization_5530 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : (¬ (formula_1547 c0_depth c0_kind c0_node c0_sign r2_level)) ↔ (¬ (shared_expr_Classification048_29 c0_depth c0_kind c0_node c0_sign r2_level)) := (not_congr (normalization_5529 c0_depth c0_kind c0_node c0_sign r2_level))

abbrev shared_expr_Classification048_30 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : Prop := ((((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification048_21 c0_depth c0_kind c0_sign r2_level))) ∨ ((¬ ((¬ ((r2_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification048_29 c0_depth c0_kind c0_node c0_sign r2_level))))
theorem normalization_5531 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : (formula_1548 c0_depth c0_kind c0_node c0_sign r2_group r2_level) ↔ (shared_expr_Classification048_30 c0_depth c0_kind c0_node c0_sign r2_group r2_level) := (or_congr (and_congr (normalization_412 r2_group) (normalization_5498 c0_depth c0_kind c0_sign r2_level)) (and_congr (not_congr (normalization_412 r2_group)) (normalization_5530 c0_depth c0_kind c0_node c0_sign r2_level)))

theorem normalization_5532 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : (¬ (formula_1548 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) ↔ (¬ (shared_expr_Classification048_30 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) := (not_congr (normalization_5531 c0_depth c0_kind c0_node c0_sign r2_group r2_level))

theorem normalization_5533 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1548 c0_depth c0_kind c0_node c0_sign r2_group r2_level))) ↔ ((¬ ((r2_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification048_30 c0_depth c0_kind c0_node c0_sign r2_group r2_level))) := (or_congr (normalization_4258 r2_mode) (or_congr (normalization_4260 r2_mode) (normalization_5532 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))

theorem normalization_5534 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : (¬ ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1548 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) ↔ (¬ ((¬ ((r2_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification048_30 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) := (not_congr (normalization_5533 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode))

abbrev shared_expr_Classification048_31 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ ((r2_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification048_20 c0_depth c0_kind c0_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification048_22 c0_depth c0_kind c0_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification048_24 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification048_26 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification048_28 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))) ∨ (¬ ((¬ ((r2_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r2_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification048_30 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))))
theorem normalization_5535 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1549 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_31 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) := (or_congr (normalization_5494 c0_depth c0_kind c0_sign r2_group r2_level r2_mode) (or_congr (normalization_5502 c0_depth c0_kind c0_sign r2_group r2_level r2_mode) (or_congr (normalization_5514 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) (or_congr (normalization_5522 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) (or_congr (normalization_5528 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) (normalization_5534 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode))))))

abbrev shared_expr_Classification048_32 (c0_depth c0_kind c0_sign r2_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification048_33 (c0_depth c0_kind c0_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification048_32 c0_depth c0_kind c0_sign r2_level)))
abbrev shared_expr_Classification048_34 (c0_depth c0_kind c0_sign r2_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification048_35 (c0_depth c0_kind c0_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification048_34 c0_depth c0_kind c0_sign r2_level)))
abbrev shared_expr_Classification048_36 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification048_37 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification048_32 c0_depth c0_kind c0_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification048_36 c0_depth c0_kind c0_node c0_sign r2_level)))
abbrev shared_expr_Classification048_38 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification048_39 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification048_32 c0_depth c0_kind c0_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification048_38 c0_depth c0_kind c0_node c0_sign r2_level)))
abbrev shared_expr_Classification048_40 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification048_41 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification048_40 c0_depth c0_kind c0_node c0_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification048_34 c0_depth c0_kind c0_sign r2_level)))
abbrev shared_expr_Classification048_42 (c0_depth c0_kind c0_node c0_sign r2_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ (((c0_depth + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification048_43 (c0_depth c0_kind c0_node c0_sign r2_group r2_level : Int) : Prop := (((((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification048_42 c0_depth c0_kind c0_node c0_sign r2_level)) ∨ ((¬ (((r2_group) ≤ (1 : Int)) ∧ (¬ ((r2_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification048_34 c0_depth c0_kind c0_sign r2_level)))
abbrev shared_expr_Classification048_44 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := (((((r2_mode) ≤ (0 : Int)) ∧ (¬ ((r2_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification048_33 c0_depth c0_kind c0_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (1 : Int)) ∧ (¬ ((r2_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification048_35 c0_depth c0_kind c0_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (2 : Int)) ∧ (¬ ((r2_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification048_37 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (3 : Int)) ∧ (¬ ((r2_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification048_39 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (4 : Int)) ∧ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification048_41 c0_depth c0_kind c0_node c0_sign r2_group r2_level)) ∨ ((((r2_mode) ≤ (5 : Int)) ∧ (¬ ((r2_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification048_43 c0_depth c0_kind c0_node c0_sign r2_group r2_level)))
theorem normalization_5536 (c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode : Int) : ((formula_1606 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) ↔ (formula_1549 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)) ↔ ((shared_expr_Classification048_44 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_31 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)) := (iff_congr (normalization_5392 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) (normalization_5535 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode))

abbrev shared_expr_Classification048_45 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := (((¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode))) ∨ ((¬ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification048_31 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)))
theorem normalization_5537 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1622 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_3515 c0_kind) (normalization_5480 c0_group c0_level c0_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_3515 c0_kind)) (normalization_5535 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)))

abbrev shared_expr_Classification048_46 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification048_15 c0_group c0_level c0_mode r2_group r2_level r2_mode)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification048_44 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)))
abbrev shared_expr_Classification048_47 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Classification048_46 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))
theorem normalization_5538 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1623 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_47 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := (iff_congr (normalization_5393 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) (normalization_5537 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))

-- Checked replay of monotonicity.
theorem replay_2599 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1623 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := by
  classical
  have ht := (normalized_1332 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) (shared_expr_Classification048_15 c0_group c0_level c0_mode r2_group r2_level r2_mode) (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode) (shared_expr_Classification048_44 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) (shared_expr_Classification048_31 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode))
  have n0 : ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3517 c0_kind) (replay_1292 c0_kind)
  have n1 : ((shared_expr_Classification048_15 c0_group c0_level c0_mode r2_group r2_level r2_mode) ↔ (¬ (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode))) := by
    exact Iff.mp (normalization_5482 c0_group c0_level c0_mode r2_group r2_level r2_mode) (replay_2597 c0_group c0_level c0_mode r2_group r2_level r2_mode)
  have n2 : ((shared_expr_Classification048_44 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_31 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)) := by
    exact Iff.mp (normalization_5536 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode) (replay_2598 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5538 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) hn

abbrev shared_expr_Classification048_48 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := ((formula_1622 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (formula_1551 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))
abbrev formula_1624 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification048_48 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)

theorem normalized_1333 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification048_49 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification048_31 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)) ∨ ((¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode))))
theorem normalization_5539 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1551 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_3514 c0_kind) (normalization_5535 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_3514 c0_kind)) (normalization_5480 c0_group c0_level c0_mode r2_group r2_level r2_mode)))

abbrev shared_expr_Classification048_50 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Classification048_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))
theorem normalization_5540 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1624 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_50 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := (iff_congr (normalization_5537 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) (normalization_5539 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))

-- Checked replay of rewrite.
theorem replay_2600 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1624 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := by
  classical
  have ht := (normalized_1333 ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) (shared_expr_Classification048_16 c0_group c0_level c0_mode r2_group r2_level r2_mode) (shared_expr_Classification048_31 c0_depth c0_kind c0_node c0_sign r2_group r2_level r2_mode))
  have hn := ht
  exact Iff.mpr (normalization_5540 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) hn

abbrev shared_expr_Classification048_51 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := ((formula_1607 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (formula_1551 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))
abbrev formula_1625 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification048_51 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)

theorem normalized_1334 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification048_52 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Classification048_46 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))
theorem normalization_5541 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1625 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) ↔ (shared_expr_Classification048_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := (iff_congr (normalization_5393 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) (normalization_5539 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))

-- Checked replay of trans.
theorem replay_2601 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) : (formula_1625 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := by
  classical
  have ht := (normalized_1334 (shared_expr_Classification048_46 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) (shared_expr_Classification048_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) (shared_expr_Classification048_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode))
  have n0 : (shared_expr_Classification048_47 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := by
    exact Iff.mp (normalization_5538 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) (replay_2599 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)
  have n1 : (shared_expr_Classification048_50 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) := by
    exact Iff.mp (normalization_5540 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) (replay_2600 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5541 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) hn

-- Checked replay of rewrite.
theorem replay_2602 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : ((formula_1610 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) ↔ (formula_152 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) := by
  classical
  first
  | (simp only [formula_1610, shared_expr_Classification047_130, formula_1608, shared_expr_Classification047_128, formula_1609, shared_expr_Classification047_129, formula_1584, shared_expr_Classification047_30, formula_1585, shared_expr_Classification047_31, formula_1586, shared_expr_Classification047_32, formula_1587, shared_expr_Classification047_33, formula_152, formula_140, formula_138, formula_139, formula_143, formula_141, formula_142, formula_145, formula_144, formula_147, formula_146, formula_149, formula_148, formula_151, formula_150, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_1335 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5542 (c0_depth r2_depth : Int) : (r2_depth ≤ c0_depth) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5543 (c0_depth r2_depth : Int) : (r2_depth ≥ c0_depth) ↔ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_5544 (c0_depth r2_depth : Int) : ((r2_depth ≤ c0_depth) ∧ (r2_depth ≥ c0_depth)) ↔ ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (and_congr (normalization_5542 c0_depth r2_depth) (normalization_5543 c0_depth r2_depth))

abbrev shared_expr_Classification048_53 (c0_depth r2_depth : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
theorem normalization_5545 (c0_depth r2_depth : Int) : ((r2_depth = c0_depth) ↔ ((r2_depth ≤ c0_depth) ∧ (r2_depth ≥ c0_depth))) ↔ (shared_expr_Classification048_53 c0_depth r2_depth) := (iff_congr (normalization_5292 c0_depth r2_depth) (normalization_5544 c0_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_2603 (c0_depth r2_depth : Int) : ((r2_depth = c0_depth) ↔ ((r2_depth ≤ c0_depth) ∧ (r2_depth ≥ c0_depth))) := by
  classical
  have ht := (normalized_1335 ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5545 c0_depth r2_depth) hn

theorem normalized_1336 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5546 (c0_depth r2_depth : Int) : ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5547 (c0_depth r2_depth : Int) : ((r2_depth ≤ c0_depth) ↔ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_5542 c0_depth r2_depth) (normalization_5546 c0_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_2604 (c0_depth r2_depth : Int) : ((r2_depth ≤ c0_depth) ↔ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1336 ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5547 c0_depth r2_depth) hn

theorem normalized_1337 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5548 (c0_depth r2_depth : Int) : ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_5549 (c0_depth r2_depth : Int) : ((r2_depth ≥ c0_depth) ↔ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (iff_congr (normalization_5543 c0_depth r2_depth) (normalization_5548 c0_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_2605 (c0_depth r2_depth : Int) : ((r2_depth ≥ c0_depth) ↔ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1337 ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5549 c0_depth r2_depth) hn

theorem normalized_1338 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5550 (c0_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∧ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (and_congr (normalization_5546 c0_depth r2_depth) (normalization_5548 c0_depth r2_depth))

theorem normalization_5551 (c0_depth r2_depth : Int) : (((r2_depth ≤ c0_depth) ∧ (r2_depth ≥ c0_depth)) ↔ (((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∧ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification048_53 c0_depth r2_depth) := (iff_congr (normalization_5544 c0_depth r2_depth) (normalization_5550 c0_depth r2_depth))

-- Checked replay of monotonicity.
theorem replay_2606 (c0_depth r2_depth : Int) : (((r2_depth ≤ c0_depth) ∧ (r2_depth ≥ c0_depth)) ↔ (((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∧ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1338 ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5547 c0_depth r2_depth) (replay_2604 c0_depth r2_depth)
  have n1 : (((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5549 c0_depth r2_depth) (replay_2605 c0_depth r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5551 c0_depth r2_depth) hn

abbrev shared_expr_Classification048_54 (c0_depth r2_depth : Int) : Prop := ((((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∧ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))))))
abbrev formula_1626 (c0_depth r2_depth : Int) : Prop := (shared_expr_Classification048_54 c0_depth r2_depth)

theorem normalized_1339 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5552 (c0_depth r2_depth : Int) : (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_5546 c0_depth r2_depth))

theorem normalization_5553 (c0_depth r2_depth : Int) : (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := (not_congr (normalization_5548 c0_depth r2_depth))

theorem normalization_5554 (c0_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := (or_congr (normalization_5552 c0_depth r2_depth) (normalization_5553 c0_depth r2_depth))

theorem normalization_5555 (c0_depth r2_depth : Int) : (¬ ((¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))) := (not_congr (normalization_5554 c0_depth r2_depth))

abbrev shared_expr_Classification048_55 (c0_depth r2_depth : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))))
theorem normalization_5556 (c0_depth r2_depth : Int) : (formula_1626 c0_depth r2_depth) ↔ (shared_expr_Classification048_55 c0_depth r2_depth) := (iff_congr (normalization_5550 c0_depth r2_depth) (normalization_5555 c0_depth r2_depth))

-- Checked replay of rewrite.
theorem replay_2607 (c0_depth r2_depth : Int) : (formula_1626 c0_depth r2_depth) := by
  classical
  have ht := (normalized_1339 ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5556 c0_depth r2_depth) hn

theorem normalized_1340 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5557 (c0_depth r2_depth : Int) : (((r2_depth ≤ c0_depth) ∧ (r2_depth ≥ c0_depth)) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification048_55 c0_depth r2_depth) := (iff_congr (normalization_5544 c0_depth r2_depth) (normalization_5555 c0_depth r2_depth))

-- Checked replay of trans.
theorem replay_2608 (c0_depth r2_depth : Int) : (((r2_depth ≤ c0_depth) ∧ (r2_depth ≥ c0_depth)) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1340 ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (shared_expr_Classification048_55 c0_depth r2_depth))
  have n0 : (shared_expr_Classification048_53 c0_depth r2_depth) := by
    exact Iff.mp (normalization_5551 c0_depth r2_depth) (replay_2606 c0_depth r2_depth)
  have n1 : (shared_expr_Classification048_55 c0_depth r2_depth) := by
    exact Iff.mp (normalization_5556 c0_depth r2_depth) (replay_2607 c0_depth r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5557 c0_depth r2_depth) hn

theorem normalized_1341 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5558 (c0_depth r2_depth : Int) : ((r2_depth = c0_depth) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification048_55 c0_depth r2_depth) := (iff_congr (normalization_5292 c0_depth r2_depth) (normalization_5555 c0_depth r2_depth))

-- Checked replay of trans.
theorem replay_2609 (c0_depth r2_depth : Int) : ((r2_depth = c0_depth) ↔ (¬ ((¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1341 ((¬ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (shared_expr_Classification048_55 c0_depth r2_depth))
  have n0 : (shared_expr_Classification048_53 c0_depth r2_depth) := by
    exact Iff.mp (normalization_5545 c0_depth r2_depth) (replay_2603 c0_depth r2_depth)
  have n1 : (shared_expr_Classification048_55 c0_depth r2_depth) := by
    exact Iff.mp (normalization_5557 c0_depth r2_depth) (replay_2608 c0_depth r2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5558 c0_depth r2_depth) hn

abbrev shared_expr_Classification048_56 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (((r2_sign = (0 : Int)) ∧ (c0_sign = (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev formula_1627 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (shared_expr_Classification048_56 c0_node c0_sign r2_node r2_sign)

theorem normalized_1342 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5559 (c0_node c0_sign r2_node r2_sign : Int) : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_311 r2_sign) (and_congr (normalization_3582 c0_sign) (normalization_5402 c0_node r2_node)))

abbrev shared_expr_Classification048_57 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ↔ ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))
theorem normalization_5560 (c0_node c0_sign r2_node r2_sign : Int) : (formula_1627 c0_node c0_sign r2_node r2_sign) ↔ (shared_expr_Classification048_57 c0_node c0_sign r2_node r2_sign) := (iff_congr (normalization_5403 c0_node c0_sign r2_node r2_sign) (normalization_5559 c0_node c0_sign r2_node r2_sign))

-- Checked replay of monotonicity.
theorem replay_2610 (c0_node c0_sign r2_node r2_sign : Int) : (formula_1627 c0_node c0_sign r2_node r2_sign) := by
  classical
  have ht := (normalized_1342 (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))) (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have n0 : ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_4294 r2_sign) (replay_1628 r2_sign)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3584 c0_sign) (replay_1316 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5560 c0_node c0_sign r2_node r2_sign) hn

abbrev shared_expr_Classification048_58 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
abbrev formula_1628 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (shared_expr_Classification048_58 c0_node c0_sign r2_node r2_sign)

theorem normalized_1343 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5561 (c0_node r2_node : Int) : (¬ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5402 c0_node r2_node))

theorem normalization_5562 (c0_node c0_sign r2_node r2_sign : Int) : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ↔ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) := (or_congr (normalization_307 r2_sign) (or_congr (normalization_309 r2_sign) (or_congr (normalization_3579 c0_sign) (or_congr (normalization_3580 c0_sign) (normalization_5561 c0_node r2_node)))))

theorem normalization_5563 (c0_node c0_sign r2_node r2_sign : Int) : (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_5562 c0_node c0_sign r2_node r2_sign))

abbrev shared_expr_Classification048_59 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))))
theorem normalization_5564 (c0_node c0_sign r2_node r2_sign : Int) : (formula_1628 c0_node c0_sign r2_node r2_sign) ↔ (shared_expr_Classification048_59 c0_node c0_sign r2_node r2_sign) := (iff_congr (normalization_5559 c0_node c0_sign r2_node r2_sign) (normalization_5563 c0_node c0_sign r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_2611 (c0_node c0_sign r2_node r2_sign : Int) : (formula_1628 c0_node c0_sign r2_node r2_sign) := by
  classical
  have ht := (normalized_1343 ((r2_sign) ≤ (0 : Int)) ((r2_sign) ≤ (-1 : Int)) ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5564 c0_node c0_sign r2_node r2_sign) hn

abbrev shared_expr_Classification048_60 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (((r2_sign = (0 : Int)) ∧ (c0_sign = (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
abbrev formula_1629 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (shared_expr_Classification048_60 c0_node c0_sign r2_node r2_sign)

theorem normalized_1344 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification048_61 (c0_node c0_sign r2_node r2_sign : Int) : Prop := (((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))))
theorem normalization_5565 (c0_node c0_sign r2_node r2_sign : Int) : (formula_1629 c0_node c0_sign r2_node r2_sign) ↔ (shared_expr_Classification048_61 c0_node c0_sign r2_node r2_sign) := (iff_congr (normalization_5403 c0_node c0_sign r2_node r2_sign) (normalization_5563 c0_node c0_sign r2_node r2_sign))

-- Checked replay of trans.
theorem replay_2612 (c0_node c0_sign r2_node r2_sign : Int) : (formula_1629 c0_node c0_sign r2_node r2_sign) := by
  classical
  have ht := (normalized_1344 ((((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ((¬ ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ((¬ ((r2_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r2_sign) ≤ (-1 : Int)))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))))
  have n0 : (shared_expr_Classification048_57 c0_node c0_sign r2_node r2_sign) := by
    exact Iff.mp (normalization_5560 c0_node c0_sign r2_node r2_sign) (replay_2610 c0_node c0_sign r2_node r2_sign)
  have n1 : (shared_expr_Classification048_59 c0_node c0_sign r2_node r2_sign) := by
    exact Iff.mp (normalization_5564 c0_node c0_sign r2_node r2_sign) (replay_2611 c0_node c0_sign r2_node r2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5565 c0_node c0_sign r2_node r2_sign) hn

theorem normalized_1345 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5566 (c0_sign : Int) : ((c0_sign ≤ (2 : Int)) ∧ (c0_sign ≥ (2 : Int))) ↔ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int)))) := (and_congr (normalization_5228 c0_sign) (normalization_5230 c0_sign))

theorem normalization_5567 (c0_sign : Int) : ((c0_sign = (2 : Int)) ↔ ((c0_sign ≤ (2 : Int)) ∧ (c0_sign ≥ (2 : Int)))) ↔ ((((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int)))) ↔ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) := (iff_congr (normalization_3218 c0_sign) (normalization_5566 c0_sign))

-- Checked replay of rewrite.
theorem replay_2613 (c0_sign : Int) : ((c0_sign = (2 : Int)) ↔ ((c0_sign ≤ (2 : Int)) ∧ (c0_sign ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_1345 (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5567 c0_sign) hn

theorem normalized_1346 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5568 (c0_sign : Int) : (((c0_sign ≤ (2 : Int)) ∧ (c0_sign ≥ (2 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ↔ ((((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_5566 c0_sign) (normalization_5233 c0_sign))

-- Checked replay of rewrite.
theorem replay_2614 (c0_sign : Int) : (((c0_sign ≤ (2 : Int)) ∧ (c0_sign ≥ (2 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_1346 ((c0_sign) ≤ (2 : Int)) ((c0_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5568 c0_sign) hn

end H4Formal.Generated.Classification
