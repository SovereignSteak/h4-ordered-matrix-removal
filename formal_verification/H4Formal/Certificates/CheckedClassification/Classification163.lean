import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification162

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_2946 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9152 (c0_level h : Int) : (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (not_congr (normalization_9148 c0_level h))

theorem normalization_9153 (c0_level h : Int) : ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int)))) ↔ ((¬ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int))))) := (or_congr (normalization_5192 c0_level h) (normalization_9152 c0_level h))

theorem normalization_9154 (c0_level h : Int) : (¬ ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))))) := (not_congr (normalization_9153 c0_level h))

abbrev shared_expr_Classification163_0 (c0_level h : Int) : Prop := ((((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))))))
theorem normalization_9155 (c0_level h : Int) : ((((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int)))))) ↔ (shared_expr_Classification163_0 c0_level h) := (iff_congr (normalization_9150 c0_level h) (normalization_9154 c0_level h))

-- Checked replay of rewrite.
theorem replay_12326 (c0_level h : Int) : ((((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_2946 ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9155 c0_level h) hn

theorem normalized_2947 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9156 (c0_level h : Int) : (((c0_level ≤ h) ∧ (c0_level ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int)))))) ↔ (shared_expr_Classification163_0 c0_level h) := (iff_congr (normalization_9145 c0_level h) (normalization_9154 c0_level h))

-- Checked replay of trans.
theorem replay_12327 (c0_level h : Int) : (((c0_level ≤ h) ∧ (c0_level ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_2947 (((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) (shared_expr_Classification163_0 c0_level h))
  have n0 : ((((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) ↔ (((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_9151 c0_level h) (replay_12325 c0_level h)
  have n1 : (shared_expr_Classification163_0 c0_level h) := by
    exact Iff.mp (normalization_9155 c0_level h) (replay_12326 c0_level h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9156 c0_level h) hn

theorem normalized_2948 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9157 (c0_level h : Int) : ((c0_level = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int)))))) ↔ (shared_expr_Classification163_0 c0_level h) := (iff_congr (normalization_9051 c0_level h) (normalization_9154 c0_level h))

-- Checked replay of trans.
theorem replay_12328 (c0_level h : Int) : ((c0_level = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_2948 (((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) (shared_expr_Classification163_0 c0_level h))
  have n0 : ((((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) ↔ (((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_9146 c0_level h) (replay_12322 c0_level h)
  have n1 : (shared_expr_Classification163_0 c0_level h) := by
    exact Iff.mp (normalization_9156 c0_level h) (replay_12327 c0_level h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9157 c0_level h) hn

theorem normalized_2949 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9158 (r0_group : Int) : ((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int))) ↔ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) := (and_congr (normalization_958 r0_group) (normalization_960 r0_group))

theorem normalization_9159 (r0_group : Int) : ((r0_group = (1 : Int)) ↔ ((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int)))) ↔ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) := (iff_congr (normalization_658 r0_group) (normalization_9158 r0_group))

-- Checked replay of rewrite.
theorem replay_12329 (r0_group : Int) : ((r0_group = (1 : Int)) ↔ ((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2949 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_9159 r0_group) hn

theorem normalized_2950 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9160 (r0_group : Int) : (((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int))) ↔ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ↔ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := (iff_congr (normalization_9158 r0_group) (normalization_3740 r0_group))

-- Checked replay of rewrite.
theorem replay_12330 (r0_group : Int) : (((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int))) ↔ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2950 ((r0_group) ≤ (1 : Int)) ((r0_group) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9160 r0_group) hn

theorem normalized_2951 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9161 (r0_group : Int) : ((r0_group = (1 : Int)) ↔ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ↔ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := (iff_congr (normalization_658 r0_group) (normalization_3740 r0_group))

-- Checked replay of trans.
theorem replay_12331 (r0_group : Int) : ((r0_group = (1 : Int)) ↔ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2951 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_9159 r0_group) (replay_12329 r0_group)
  have n1 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_9160 r0_group) (replay_12330 r0_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9161 r0_group) hn

theorem normalized_2952 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9162 (r1_group : Int) : ((r1_group ≤ (2 : Int)) ∧ (r1_group ≥ (2 : Int))) ↔ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) := (and_congr (normalization_90 r1_group) (normalization_92 r1_group))

theorem normalization_9163 (r1_group : Int) : ((r1_group = (2 : Int)) ↔ ((r1_group ≤ (2 : Int)) ∧ (r1_group ≥ (2 : Int)))) ↔ ((((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ↔ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int))))) := (iff_congr (normalization_6 r1_group) (normalization_9162 r1_group))

-- Checked replay of rewrite.
theorem replay_12332 (r1_group : Int) : ((r1_group = (2 : Int)) ↔ ((r1_group ≤ (2 : Int)) ∧ (r1_group ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_2952 (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_9163 r1_group) hn

theorem normalized_2953 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9164 (r1_group : Int) : (((r1_group ≤ (2 : Int)) ∧ (r1_group ≥ (2 : Int))) ↔ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))))) ↔ ((((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int))))))) := (iff_congr (normalization_9162 r1_group) (normalization_95 r1_group))

-- Checked replay of rewrite.
theorem replay_12333 (r1_group : Int) : (((r1_group ≤ (2 : Int)) ∧ (r1_group ≥ (2 : Int))) ↔ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_2953 ((r1_group) ≤ (2 : Int)) ((r1_group) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9164 r1_group) hn

theorem normalized_2954 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9165 (r1_group : Int) : ((r1_group = (2 : Int)) ↔ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))))) ↔ ((((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int))))))) := (iff_congr (normalization_6 r1_group) (normalization_95 r1_group))

-- Checked replay of trans.
theorem replay_12334 (r1_group : Int) : ((r1_group = (2 : Int)) ↔ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_2954 (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ((((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int))))))))
  have n0 : ((((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ↔ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_9163 r1_group) (replay_12332 r1_group)
  have n1 : ((((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_9164 r1_group) (replay_12333 r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9165 r1_group) hn

theorem normalized_2955 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9166 (c0_group : Int) : ((c0_group ≤ (1 : Int)) ∧ (c0_group ≥ (1 : Int))) ↔ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) := (and_congr (normalization_5193 c0_group) (normalization_5195 c0_group))

theorem normalization_9167 (c0_group : Int) : ((c0_group = (1 : Int)) ↔ ((c0_group ≤ (1 : Int)) ∧ (c0_group ≥ (1 : Int)))) ↔ ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ↔ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) := (iff_congr (normalization_3248 c0_group) (normalization_9166 c0_group))

-- Checked replay of rewrite.
theorem replay_12335 (c0_group : Int) : ((c0_group = (1 : Int)) ↔ ((c0_group ≤ (1 : Int)) ∧ (c0_group ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2955 (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_9167 c0_group) hn

theorem normalized_2956 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9168 (c0_group : Int) : (((c0_group ≤ (1 : Int)) ∧ (c0_group ≥ (1 : Int))) ↔ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) ↔ ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))))) := (iff_congr (normalization_9166 c0_group) (normalization_5198 c0_group))

-- Checked replay of rewrite.
theorem replay_12336 (c0_group : Int) : (((c0_group ≤ (1 : Int)) ∧ (c0_group ≥ (1 : Int))) ↔ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2956 ((c0_group) ≤ (1 : Int)) ((c0_group) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9168 c0_group) hn

theorem normalized_2957 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9169 (c0_group : Int) : ((c0_group = (1 : Int)) ↔ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) ↔ ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))))) := (iff_congr (normalization_3248 c0_group) (normalization_5198 c0_group))

-- Checked replay of trans.
theorem replay_12337 (c0_group : Int) : ((c0_group = (1 : Int)) ↔ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2957 (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))))))
  have n0 : ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ↔ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_9167 c0_group) (replay_12335 c0_group)
  have n1 : ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_9168 c0_group) (replay_12336 c0_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9169 c0_group) hn

theorem normalized_2958 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9170 (r2_kind : Int) : ((r2_kind ≤ (1 : Int)) ∧ (r2_kind ≥ (1 : Int))) ↔ (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) := (and_congr (normalization_424 r2_kind) (normalization_426 r2_kind))

theorem normalization_9171 (r2_kind : Int) : ((r2_kind = (1 : Int)) ↔ ((r2_kind ≤ (1 : Int)) ∧ (r2_kind ≥ (1 : Int)))) ↔ ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ↔ (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int))))) := (iff_congr (normalization_148 r2_kind) (normalization_9170 r2_kind))

-- Checked replay of rewrite.
theorem replay_12338 (r2_kind : Int) : ((r2_kind = (1 : Int)) ↔ ((r2_kind ≤ (1 : Int)) ∧ (r2_kind ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2958 (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_9171 r2_kind) hn

theorem normalized_2959 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9172 (r2_kind : Int) : ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int)))) ↔ ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int))))) := (or_congr (normalization_425 r2_kind) (normalization_427 r2_kind))

theorem normalization_9173 (r2_kind : Int) : (¬ ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))))) ↔ (¬ ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int)))))) := (not_congr (normalization_9172 r2_kind))

theorem normalization_9174 (r2_kind : Int) : (((r2_kind ≤ (1 : Int)) ∧ (r2_kind ≥ (1 : Int))) ↔ (¬ ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int)))))) ↔ ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_9170 r2_kind) (normalization_9173 r2_kind))

-- Checked replay of rewrite.
theorem replay_12339 (r2_kind : Int) : (((r2_kind ≤ (1 : Int)) ∧ (r2_kind ≥ (1 : Int))) ↔ (¬ ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2959 ((r2_kind) ≤ (1 : Int)) ((r2_kind) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9174 r2_kind) hn

theorem normalized_2960 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9175 (r2_kind : Int) : ((r2_kind = (1 : Int)) ↔ (¬ ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int)))))) ↔ ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_148 r2_kind) (normalization_9173 r2_kind))

-- Checked replay of trans.
theorem replay_12340 (r2_kind : Int) : ((r2_kind = (1 : Int)) ↔ (¬ ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2960 (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int))))))))
  have n0 : ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ↔ (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_9171 r2_kind) (replay_12338 r2_kind)
  have n1 : ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_9174 r2_kind) (replay_12339 r2_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9175 r2_kind) hn

theorem normalized_2961 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9176 (c2_depth h : Int) : (c2_depth ≥ h) ↔ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) := by
  omega

theorem normalization_9177 (c2_depth h : Int) : ((c2_depth ≤ h) ∧ (c2_depth ≥ h)) ↔ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (and_congr (normalization_2129 c2_depth h) (normalization_9176 c2_depth h))

theorem normalization_9178 (c2_depth h : Int) : ((c2_depth = h) ↔ ((c2_depth ≤ h) ∧ (c2_depth ≥ h))) ↔ ((((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ↔ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) := (iff_congr (normalization_2132 c2_depth h) (normalization_9177 c2_depth h))

-- Checked replay of rewrite.
theorem replay_12341 (c2_depth h : Int) : ((c2_depth = h) ↔ ((c2_depth ≤ h) ∧ (c2_depth ≥ h))) := by
  classical
  have ht := (normalized_2961 (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_9178 c2_depth h) hn

theorem normalized_2962 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9179 (c2_depth h : Int) : ((c2_depth ≤ h) ↔ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int))) := (iff_congr (normalization_2129 c2_depth h) (normalization_2152 c2_depth h))

-- Checked replay of rewrite.
theorem replay_12342 (c2_depth h : Int) : ((c2_depth ≤ h) ↔ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2962 ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9179 c2_depth h) hn

theorem normalized_2963 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9180 (c2_depth h : Int) : ((c2_depth ≥ h) ↔ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ ((¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (iff_congr (normalization_9176 c2_depth h) (normalization_2190 c2_depth h))

-- Checked replay of rewrite.
theorem replay_12343 (c2_depth h : Int) : ((c2_depth ≥ h) ↔ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2963 ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9180 c2_depth h) hn

theorem normalized_2964 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9181 (c2_depth h : Int) : (((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (and_congr (normalization_2152 c2_depth h) (normalization_2190 c2_depth h))

theorem normalization_9182 (c2_depth h : Int) : (((c2_depth ≤ h) ∧ (c2_depth ≥ h)) ↔ (((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ ((((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ↔ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) := (iff_congr (normalization_9177 c2_depth h) (normalization_9181 c2_depth h))

-- Checked replay of monotonicity.
theorem replay_12344 (c2_depth h : Int) : (((c2_depth ≤ h) ∧ (c2_depth ≥ h)) ↔ (((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := by
  classical
  have ht := (normalized_2964 ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
  have n0 : (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ↔ ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_9179 c2_depth h) (replay_12342 c2_depth h)
  have n1 : ((¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) ↔ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_9180 c2_depth h) (replay_12343 c2_depth h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9182 c2_depth h) hn

theorem normalized_2965 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9183 (c2_depth h : Int) : (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))) := (not_congr (normalization_2192 c2_depth h))

abbrev shared_expr_Classification163_1 (c2_depth h : Int) : Prop := ((((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))))
theorem normalization_9184 (c2_depth h : Int) : ((((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Classification163_1 c2_depth h) := (iff_congr (normalization_9181 c2_depth h) (normalization_9183 c2_depth h))

-- Checked replay of rewrite.
theorem replay_12345 (c2_depth h : Int) : ((((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_2965 ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9184 c2_depth h) hn

theorem normalized_2966 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9185 (c2_depth h : Int) : (((c2_depth ≤ h) ∧ (c2_depth ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Classification163_1 c2_depth h) := (iff_congr (normalization_9177 c2_depth h) (normalization_9183 c2_depth h))

-- Checked replay of trans.
theorem replay_12346 (c2_depth h : Int) : (((c2_depth ≤ h) ∧ (c2_depth ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_2966 (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) (shared_expr_Classification163_1 c2_depth h))
  have n0 : ((((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ↔ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_9182 c2_depth h) (replay_12344 c2_depth h)
  have n1 : (shared_expr_Classification163_1 c2_depth h) := by
    exact Iff.mp (normalization_9184 c2_depth h) (replay_12345 c2_depth h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9185 c2_depth h) hn

theorem normalized_2967 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9186 (c2_depth h : Int) : ((c2_depth = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Classification163_1 c2_depth h) := (iff_congr (normalization_2132 c2_depth h) (normalization_9183 c2_depth h))

-- Checked replay of trans.
theorem replay_12347 (c2_depth h : Int) : ((c2_depth = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_2967 (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) (shared_expr_Classification163_1 c2_depth h))
  have n0 : ((((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ↔ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_9178 c2_depth h) (replay_12341 c2_depth h)
  have n1 : (shared_expr_Classification163_1 c2_depth h) := by
    exact Iff.mp (normalization_9185 c2_depth h) (replay_12346 c2_depth h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9186 c2_depth h) hn

theorem normalized_2968 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9187 (c2_node r2_node : Int) : (r2_node ≥ c2_node) ↔ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_9188 (c2_node r2_node : Int) : ((r2_node ≤ c2_node) ∧ (r2_node ≥ c2_node)) ↔ ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := (and_congr (normalization_4014 c2_node r2_node) (normalization_9187 c2_node r2_node))

abbrev shared_expr_Classification163_2 (c2_node r2_node : Int) : Prop := (((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ↔ ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
theorem normalization_9189 (c2_node r2_node : Int) : ((r2_node = c2_node) ↔ ((r2_node ≤ c2_node) ∧ (r2_node ≥ c2_node))) ↔ (shared_expr_Classification163_2 c2_node r2_node) := (iff_congr (normalization_9052 c2_node r2_node) (normalization_9188 c2_node r2_node))

-- Checked replay of rewrite.
theorem replay_12348 (c2_node r2_node : Int) : ((r2_node = c2_node) ↔ ((r2_node ≤ c2_node) ∧ (r2_node ≥ c2_node))) := by
  classical
  have ht := (normalized_2968 ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_9189 c2_node r2_node) hn

theorem normalized_2969 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9190 (c2_node r2_node : Int) : ((r2_node ≤ c2_node) ↔ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_4014 c2_node r2_node) (normalization_4123 c2_node r2_node))

-- Checked replay of rewrite.
theorem replay_12349 (c2_node r2_node : Int) : ((r2_node ≤ c2_node) ↔ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_2969 ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9190 c2_node r2_node) hn

theorem normalized_2970 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9191 (c2_node r2_node : Int) : ((r2_node ≥ c2_node) ↔ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := (iff_congr (normalization_9187 c2_node r2_node) (normalization_4126 c2_node r2_node))

-- Checked replay of rewrite.
theorem replay_12350 (c2_node r2_node : Int) : ((r2_node ≥ c2_node) ↔ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_2970 ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9191 c2_node r2_node) hn

theorem normalized_2971 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9192 (c2_node r2_node : Int) : (((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := (and_congr (normalization_4123 c2_node r2_node) (normalization_4126 c2_node r2_node))

theorem normalization_9193 (c2_node r2_node : Int) : (((r2_node ≤ c2_node) ∧ (r2_node ≥ c2_node)) ↔ (((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification163_2 c2_node r2_node) := (iff_congr (normalization_9188 c2_node r2_node) (normalization_9192 c2_node r2_node))

-- Checked replay of monotonicity.
theorem replay_12351 (c2_node r2_node : Int) : (((r2_node ≤ c2_node) ∧ (r2_node ≥ c2_node)) ↔ (((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2971 ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))
  have n0 : ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ↔ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_9190 c2_node r2_node) (replay_12349 c2_node r2_node)
  have n1 : (((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ↔ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_9191 c2_node r2_node) (replay_12350 c2_node r2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9193 c2_node r2_node) hn

abbrev shared_expr_Classification163_3 (c2_node r2_node : Int) : Prop := ((((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))))
abbrev formula_3453 (c2_node r2_node : Int) : Prop := (shared_expr_Classification163_3 c2_node r2_node)

theorem normalized_2972 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9194 (c2_node r2_node : Int) : ((¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ ((¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) := (or_congr (normalization_4297 c2_node r2_node) (normalization_4127 c2_node r2_node))

theorem normalization_9195 (c2_node r2_node : Int) : (¬ ((¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))) := (not_congr (normalization_9194 c2_node r2_node))

abbrev shared_expr_Classification163_4 (c2_node r2_node : Int) : Prop := (((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))))
theorem normalization_9196 (c2_node r2_node : Int) : (formula_3453 c2_node r2_node) ↔ (shared_expr_Classification163_4 c2_node r2_node) := (iff_congr (normalization_9192 c2_node r2_node) (normalization_9195 c2_node r2_node))

-- Checked replay of rewrite.
theorem replay_12352 (c2_node r2_node : Int) : (formula_3453 c2_node r2_node) := by
  classical
  have ht := (normalized_2972 ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9196 c2_node r2_node) hn

theorem normalized_2973 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9197 (c2_node r2_node : Int) : (((r2_node ≤ c2_node) ∧ (r2_node ≥ c2_node)) ↔ (¬ ((¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification163_4 c2_node r2_node) := (iff_congr (normalization_9188 c2_node r2_node) (normalization_9195 c2_node r2_node))

-- Checked replay of trans.
theorem replay_12353 (c2_node r2_node : Int) : (((r2_node ≤ c2_node) ∧ (r2_node ≥ c2_node)) ↔ (¬ ((¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2973 ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) (shared_expr_Classification163_4 c2_node r2_node))
  have n0 : (shared_expr_Classification163_2 c2_node r2_node) := by
    exact Iff.mp (normalization_9193 c2_node r2_node) (replay_12351 c2_node r2_node)
  have n1 : (shared_expr_Classification163_4 c2_node r2_node) := by
    exact Iff.mp (normalization_9196 c2_node r2_node) (replay_12352 c2_node r2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9197 c2_node r2_node) hn

theorem normalized_2974 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9198 (c2_node r2_node : Int) : ((r2_node = c2_node) ↔ (¬ ((¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification163_4 c2_node r2_node) := (iff_congr (normalization_9052 c2_node r2_node) (normalization_9195 c2_node r2_node))

-- Checked replay of trans.
theorem replay_12354 (c2_node r2_node : Int) : ((r2_node = c2_node) ↔ (¬ ((¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_2974 ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) (shared_expr_Classification163_4 c2_node r2_node))
  have n0 : (shared_expr_Classification163_2 c2_node r2_node) := by
    exact Iff.mp (normalization_9189 c2_node r2_node) (replay_12348 c2_node r2_node)
  have n1 : (shared_expr_Classification163_4 c2_node r2_node) := by
    exact Iff.mp (normalization_9197 c2_node r2_node) (replay_12353 c2_node r2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9198 c2_node r2_node) hn

theorem normalized_2975 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9199 (c3_depth h : Int) : ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ↔ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) := by
  omega

theorem normalization_9200 (c3_depth h : Int) : ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ↔ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) := by
  omega

theorem normalization_9201 (c3_depth h : Int) : (((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) := (and_congr (normalization_9199 c3_depth h) (normalization_9200 c3_depth h))

theorem normalization_9202 (c3_depth h : Int) : (((h + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ (((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (iff_congr (normalization_9072 c3_depth h) (normalization_9201 c3_depth h))

-- Checked replay of rewrite.
theorem replay_12355 (c3_depth h : Int) : (((h + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_2975 ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_9202 c3_depth h) hn

theorem normalized_2976 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9203 (c3_depth h : Int) : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)))) := (not_congr (normalization_9199 c3_depth h))

theorem normalization_9204 (c3_depth h : Int) : (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) := (not_congr (normalization_9200 c3_depth h))

theorem normalization_9205 (c3_depth h : Int) : ((¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (or_congr (normalization_9203 c3_depth h) (normalization_9204 c3_depth h))

theorem normalization_9206 (c3_depth h : Int) : (¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) := (not_congr (normalization_9205 c3_depth h))

abbrev shared_expr_Classification163_5 (c3_depth h : Int) : Prop := (((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))))
theorem normalization_9207 (c3_depth h : Int) : ((((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification163_5 c3_depth h) := (iff_congr (normalization_9201 c3_depth h) (normalization_9206 c3_depth h))

-- Checked replay of rewrite.
theorem replay_12356 (c3_depth h : Int) : ((((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2976 ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9207 c3_depth h) hn

theorem normalized_2977 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9208 (c3_depth h : Int) : (((h + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification163_5 c3_depth h) := (iff_congr (normalization_9072 c3_depth h) (normalization_9206 c3_depth h))

-- Checked replay of trans.
theorem replay_12357 (c3_depth h : Int) : (((h + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_2977 ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) (shared_expr_Classification163_5 c3_depth h))
  have n0 : (((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) ↔ ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_9202 c3_depth h) (replay_12355 c3_depth h)
  have n1 : (shared_expr_Classification163_5 c3_depth h) := by
    exact Iff.mp (normalization_9207 c3_depth h) (replay_12356 c3_depth h)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9208 c3_depth h) hn

theorem normalized_2978 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9209 (c3_node r2_node : Int) : (((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (and_congr (normalization_8423 c3_node r2_node) (normalization_8421 c3_node r2_node))

abbrev shared_expr_Classification163_6 (c3_node r2_node : Int) : Prop := (((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
theorem normalization_9210 (c3_node r2_node : Int) : (((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification163_6 c3_node r2_node) := (iff_congr (normalization_9073 c3_node r2_node) (normalization_9209 c3_node r2_node))

-- Checked replay of rewrite.
theorem replay_12358 (c3_node r2_node : Int) : (((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) = (0 : Int)) ↔ (((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_2978 ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_9210 c3_node r2_node) hn

abbrev shared_expr_Classification163_7 (c3_node r2_node : Int) : Prop := ((((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_3454 (c3_node r2_node : Int) : Prop := (shared_expr_Classification163_7 c3_node r2_node)

theorem normalized_2979 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9211 (c3_node r2_node : Int) : (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := (not_congr (normalization_8421 c3_node r2_node))

theorem normalization_9212 (c3_node r2_node : Int) : ((¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) := (or_congr (normalization_8424 c3_node r2_node) (normalization_9211 c3_node r2_node))

theorem normalization_9213 (c3_node r2_node : Int) : (¬ ((¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) := (not_congr (normalization_9212 c3_node r2_node))

abbrev shared_expr_Classification163_8 (c3_node r2_node : Int) : Prop := (((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))))
theorem normalization_9214 (c3_node r2_node : Int) : (formula_3454 c3_node r2_node) ↔ (shared_expr_Classification163_8 c3_node r2_node) := (iff_congr (normalization_9209 c3_node r2_node) (normalization_9213 c3_node r2_node))

-- Checked replay of rewrite.
theorem replay_12359 (c3_node r2_node : Int) : (formula_3454 c3_node r2_node) := by
  classical
  have ht := (normalized_2979 (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9214 c3_node r2_node) hn

abbrev shared_expr_Classification163_9 (c3_node r2_node : Int) : Prop := (((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_3455 (c3_node r2_node : Int) : Prop := (shared_expr_Classification163_9 c3_node r2_node)

theorem normalized_2980 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9215 (c3_node r2_node : Int) : (formula_3455 c3_node r2_node) ↔ (shared_expr_Classification163_8 c3_node r2_node) := (iff_congr (normalization_9073 c3_node r2_node) (normalization_9213 c3_node r2_node))

-- Checked replay of trans.
theorem replay_12360 (c3_node r2_node : Int) : (formula_3455 c3_node r2_node) := by
  classical
  have ht := (normalized_2980 ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) (shared_expr_Classification163_8 c3_node r2_node))
  have n0 : (shared_expr_Classification163_6 c3_node r2_node) := by
    exact Iff.mp (normalization_9210 c3_node r2_node) (replay_12358 c3_node r2_node)
  have n1 : (shared_expr_Classification163_8 c3_node r2_node) := by
    exact Iff.mp (normalization_9214 c3_node r2_node) (replay_12359 c3_node r2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9215 c3_node r2_node) hn

abbrev shared_expr_Classification163_10 (c1_group c1_kind c1_level c1_mode h r0_mode : Int) : Prop := ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))) ∨ (¬ (c1_group ≤ (2 : Int))) ∨ (¬ (c1_group ≥ (2 : Int))) ∨ (¬ ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c1_level)) ≤ (0 : Int))))
abbrev formula_3456 (c1_group c1_kind c1_level c1_mode h r0_mode : Int) : Prop := (shared_expr_Classification163_10 c1_group c1_kind c1_level c1_mode h r0_mode)

abbrev shared_expr_Classification163_11 (c1_depth c1_kind c1_node h r2_node : Int) : Prop := (((r2_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∨ (¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (((c1_node % (2 : Int)) + ((-1 : Int) * (r2_node % (2 : Int)))) ≤ (0 : Int))) ∨ (¬ (((c1_node % (2 : Int)) + ((-1 : Int) * (r2_node % (2 : Int)))) ≥ (0 : Int))))
abbrev formula_3457 (c1_depth c1_kind c1_node h r2_node : Int) : Prop := (shared_expr_Classification163_11 c1_depth c1_kind c1_node h r2_node)

abbrev shared_expr_Classification163_12 (c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node : Int) : Prop := ((formula_3447 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node) ↔ ((¬ (formula_3456 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (formula_3457 c1_depth c1_kind c1_node h r2_node))))
abbrev formula_3458 (c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node : Int) : Prop := (shared_expr_Classification163_12 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node)

theorem normalized_2981 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7))) ∨ ((p8 ∧ (¬ p0)) ∧ (p9 ∧ (¬ p10)) ∧ (¬ (¬ p11)) ∧ ((¬ p12) ∧ p13))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ p4) ∨ (¬ (¬ p3)) ∨ (¬ p2) ∨ (¬ (¬ p5)))) ∨ (¬ ((¬ p11) ∨ (¬ p8) ∨ (¬ (¬ p0)) ∨ (¬ p9) ∨ (¬ (¬ p10)) ∨ (¬ (¬ p12)) ∨ (¬ p13))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9216 (c1_level h : Int) : ((h + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * h)) ≤ (-1 : Int))) := by
  omega

theorem normalization_9217 (c1_level h : Int) : (¬ ((h + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (not_congr (normalization_9216 c1_level h))

abbrev shared_expr_Classification163_13 (c1_group c1_kind c1_level c1_mode h r0_mode : Int) : Prop := ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (¬ ((c1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * h)) ≤ (-1 : Int)))))
theorem normalization_9218 (c1_group c1_kind c1_level c1_mode h r0_mode : Int) : (formula_3456 c1_group c1_kind c1_level c1_mode h r0_mode) ↔ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode) := (or_congr (normalization_1520 c1_kind) (or_congr (normalization_1521 c1_kind) (or_congr (normalization_2262 c1_group) (or_congr (normalization_2264 c1_group) (or_congr (normalization_2259 c1_level h) (or_congr (normalization_1536 c1_mode r0_mode) (or_congr (normalization_1537 c1_mode r0_mode) (normalization_9217 c1_level h))))))))

theorem normalization_9219 (c1_group c1_kind c1_level c1_mode h r0_mode : Int) : (¬ (formula_3456 c1_group c1_kind c1_level c1_mode h r0_mode)) ↔ (¬ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode)) := (not_congr (normalization_9218 c1_group c1_kind c1_level c1_mode h r0_mode))

theorem normalization_9220 (c1_node r2_node : Int) : (((c1_node % (2 : Int)) + ((-1 : Int) * (r2_node % (2 : Int)))) ≤ (0 : Int)) ↔ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (-1 : Int))) := by
  omega

theorem normalization_9221 (c1_node r2_node : Int) : (¬ (((c1_node % (2 : Int)) + ((-1 : Int) * (r2_node % (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (-1 : Int)))) := (not_congr (normalization_9220 c1_node r2_node))

theorem normalization_9222 (c1_node r2_node : Int) : (((c1_node % (2 : Int)) + ((-1 : Int) * (r2_node % (2 : Int)))) ≥ (0 : Int)) ↔ ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (0 : Int)) := by
  omega

theorem normalization_9223 (c1_node r2_node : Int) : (¬ (((c1_node % (2 : Int)) + ((-1 : Int) * (r2_node % (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (0 : Int))) := (not_congr (normalization_9222 c1_node r2_node))

abbrev shared_expr_Classification163_14 (c1_depth c1_kind c1_node h r2_node : Int) : Prop := ((¬ ((c1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (-1 : Int)))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (0 : Int))))
theorem normalization_9224 (c1_depth c1_kind c1_node h r2_node : Int) : (formula_3457 c1_depth c1_kind c1_node h r2_node) ↔ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node) := (or_congr (normalization_3940 c1_node r2_node) (or_congr (normalization_1588 c1_kind) (or_congr (normalization_1590 c1_kind) (or_congr (normalization_2271 c1_depth h) (or_congr (normalization_2277 c1_depth h) (or_congr (normalization_9221 c1_node r2_node) (normalization_9223 c1_node r2_node)))))))

theorem normalization_9225 (c1_depth c1_kind c1_node h r2_node : Int) : (¬ (formula_3457 c1_depth c1_kind c1_node h r2_node)) ↔ (¬ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node)) := (not_congr (normalization_9224 c1_depth c1_kind c1_node h r2_node))

theorem normalization_9226 (c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node : Int) : ((¬ (formula_3456 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (formula_3457 c1_depth c1_kind c1_node h r2_node))) ↔ ((¬ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node))) := (or_congr (normalization_9219 c1_group c1_kind c1_level c1_mode h r0_mode) (normalization_9225 c1_depth c1_kind c1_node h r2_node))

abbrev shared_expr_Classification163_15 (c1_group c1_kind c1_level c1_mode h r0_mode : Int) : Prop := ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (((c1_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) ∧ (¬ ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∧ (((c1_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c1_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∧ (((c1_group) ≤ (2 : Int)) ∧ (¬ ((c1_group) ≤ (1 : Int)))))
abbrev shared_expr_Classification163_16 (c1_node r2_node : Int) : Prop := ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (0 : Int)))
abbrev shared_expr_Classification163_17 (c1_depth c1_kind c1_node h r2_node : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification163_16 c1_node r2_node))
abbrev shared_expr_Classification163_18 (c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node : Int) : Prop := (((shared_expr_Classification163_15 c1_group c1_kind c1_level c1_mode h r0_mode) ∨ (shared_expr_Classification163_17 c1_depth c1_kind c1_node h r2_node)) ↔ ((¬ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node))))
theorem normalization_9227 (c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node : Int) : (formula_3458 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node) ↔ (shared_expr_Classification163_18 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node) := (iff_congr (normalization_9077 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node) (normalization_9226 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node))

-- Checked replay of rewrite.
theorem replay_12361 (c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node : Int) : (formula_3458 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node) := by
  classical
  have ht := (normalized_2981 ((c1_kind) ≤ (0 : Int)) ((c1_kind) ≤ (-1 : Int)) ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)) ((c1_level + ((-1 : Int) * h)) ≤ (0 : Int)) ((c1_level + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c1_group) ≤ (2 : Int)) ((c1_group) ≤ (1 : Int)) ((c1_kind) ≤ (1 : Int)) ((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (-1 : Int)) ((((2 : Int) * (c1_node / (2 : Int))) + ((-2 : Int) * (r2_node / (2 : Int))) + ((-1 : Int) * c1_node) + r2_node) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_9227 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node) hn

abbrev shared_expr_Classification163_19 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∧ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∧ ((¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))))) ∨ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int)))))) ∧ (¬ ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((r0_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int))))) ∧ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))) ∧ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∧ (¬ ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) ∧ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∧ (¬ ((¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ ((¬ (formula_3456 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (formula_3457 c1_depth c1_kind c1_node h r2_node))))
abbrev formula_3459 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (shared_expr_Classification163_19 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)

abbrev shared_expr_Classification163_20 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((formula_3448 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (formula_3459 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
abbrev formula_3460 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (shared_expr_Classification163_20 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)

theorem normalized_2982 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5)) ∧ (p6 ↔ p7) ∧ (p8 ↔ (¬ p9)) ∧ (p10 ↔ (¬ p11)) ∧ (p12 ↔ (¬ p13)) ∧ (p14 ↔ (¬ p15)) ∧ (p16 ↔ (¬ p17)) ∧ (p18 ↔ (¬ p19)) ∧ (p20 ↔ (¬ p21)) ∧ (p22 ↔ (¬ p23)) ∧ (p24 ↔ (¬ p25)) ∧ (p26 ↔ (¬ p27)) ∧ (p28 ↔ (¬ p29)) ∧ (p30 ↔ (¬ p31)) ∧ (p32 ↔ (¬ p33)) ∧ (p34 ↔ (¬ p35)) ∧ (p36 ↔ (¬ p37)) ∧ (p38 ↔ (¬ p39)) ∧ (p40 ↔ (¬ p41)) ∧ (p42 ↔ (¬ p43)) ∧ (p44 ↔ p45)) → ((p0 ∧ p2 ∧ p4 ∧ p6 ∧ p8 ∧ p10 ∧ p12 ∧ p14 ∧ p16 ∧ p18 ∧ p20 ∧ p22 ∧ p24 ∧ p26 ∧ p28 ∧ p30 ∧ p32 ∧ p34 ∧ p36 ∧ p38 ∧ p40 ∧ p42 ∧ p44) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p5) ∧ p7 ∧ (¬ p9) ∧ (¬ p11) ∧ (¬ p13) ∧ (¬ p15) ∧ (¬ p17) ∧ (¬ p19) ∧ (¬ p21) ∧ (¬ p23) ∧ (¬ p25) ∧ (¬ p27) ∧ (¬ p29) ∧ (¬ p31) ∧ (¬ p33) ∧ (¬ p35) ∧ (¬ p37) ∧ (¬ p39) ∧ (¬ p41) ∧ (¬ p43) ∧ p45))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification163_21 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∨ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))) ∧ (¬ ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int))))) ∧ (¬ ((¬ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) ∧ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∧ ((¬ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node))))
theorem normalization_9228 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3459 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_21 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := (and_congr (normalization_880 r0_kind) (and_congr (normalization_241 r1_kind) (and_congr (normalization_3515 c0_kind) (and_congr (normalization_9085 r0_mode) (and_congr (normalization_9095 r0_mode r1_mode) (and_congr (normalization_9112 c0_mode r0_mode) (and_congr (normalization_9126 h r0_level) (and_congr (normalization_9140 h r1_level) (and_congr (normalization_9154 c0_level h) (and_congr (normalization_3740 r0_group) (and_congr (normalization_95 r1_group) (and_congr (normalization_5198 c0_group) (and_congr (normalization_9173 r2_kind) (and_congr (normalization_4313 h r2_depth) (and_congr (normalization_599 r3_kind) (and_congr (normalization_1975 c2_kind) (and_congr (normalization_9183 c2_depth h) (and_congr (normalization_9195 c2_node r2_node) (and_congr (normalization_7284 c3_kind) (and_congr (normalization_9206 c3_depth h) (and_congr (normalization_6849 c3_sign) (and_congr (normalization_9213 c3_node r2_node) (normalization_9226 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node)))))))))))))))))))))))

abbrev shared_expr_Classification163_22 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ ((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int))))) ∧ (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∧ ((¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ∧ ((¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∧ ((¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∧ (((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∧ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ∧ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ∧ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ∧ (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∧ ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ∧ ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ∧ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ ((shared_expr_Classification163_15 c1_group c1_kind c1_level c1_mode h r0_mode) ∨ (shared_expr_Classification163_17 c1_depth c1_kind c1_node h r2_node)))
abbrev shared_expr_Classification163_23 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((shared_expr_Classification163_22 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_21 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
theorem normalization_9229 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3460 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_23 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := (iff_congr (normalization_9078 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (normalization_9228 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification163_24 (r0_mode : Int) : Prop := (((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int))))) ↔ ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∨ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))))
abbrev shared_expr_Classification163_25 (r0_mode r1_mode : Int) : Prop := ((((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))))))
abbrev shared_expr_Classification163_26 (c0_mode r0_mode : Int) : Prop := (((¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))))))
abbrev shared_expr_Classification163_27 (h r0_level : Int) : Prop := (((¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int))))))
abbrev shared_expr_Classification163_28 (h r1_level : Int) : Prop := (((¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int))))))
abbrev shared_expr_Classification163_29 (h r2_depth : Int) : Prop := (((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))))))
theorem replay_12362 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3460 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
  classical
  have ht := (normalized_2982 (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))) (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))) (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) ((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int))))) ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∨ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))) (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))) ((¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ((¬ (¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)))) ((¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ((¬ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int)))) ((¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ((¬ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int)))) (((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) ((¬ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int))))) (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int))))) (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))) (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int))))) ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) (((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))) (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) (((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ((¬ ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int))))) ((¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ((¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))) ((¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int))) ∧ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) ((¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))) ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ((¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ((shared_expr_Classification163_15 c1_group c1_kind c1_level c1_mode h r0_mode) ∨ (shared_expr_Classification163_17 c1_depth c1_kind c1_node h r2_node)) ((¬ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node))))
  have n0 : ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_882 r0_kind) (replay_465 r0_kind)
  have n1 : ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_243 r1_kind) (replay_63 r1_kind)
  have n2 : ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3517 c0_kind) (replay_1292 c0_kind)
  have n3 : (shared_expr_Classification163_24 r0_mode) := by
    exact Iff.mp (normalization_9086 r0_mode) (replay_12293 r0_mode)
  have n4 : (shared_expr_Classification163_25 r0_mode r1_mode) := by
    exact Iff.mp (normalization_9098 r0_mode r1_mode) (replay_12300 r0_mode r1_mode)
  have n5 : (shared_expr_Classification163_26 c0_mode r0_mode) := by
    exact Iff.mp (normalization_9115 c0_mode r0_mode) (replay_12307 c0_mode r0_mode)
  have n6 : (shared_expr_Classification163_27 h r0_level) := by
    exact Iff.mp (normalization_9129 h r0_level) (replay_12314 h r0_level)
  have n7 : (shared_expr_Classification163_28 h r1_level) := by
    exact Iff.mp (normalization_9143 h r1_level) (replay_12321 h r1_level)
  have n8 : (shared_expr_Classification163_0 c0_level h) := by
    exact Iff.mp (normalization_9157 c0_level h) (replay_12328 c0_level h)
  have n9 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_9161 r0_group) (replay_12331 r0_group)
  have n10 : ((((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_9165 r1_group) (replay_12334 r1_group)
  have n11 : ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_9169 c0_group) (replay_12337 c0_group)
  have n12 : ((((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_9175 r2_kind) (replay_12340 r2_kind)
  have n13 : (shared_expr_Classification163_29 h r2_depth) := by
    exact Iff.mp (normalization_4316 h r2_depth) (replay_1641 h r2_depth)
  have n14 : ((((r3_kind) ≤ (2 : Int)) ∧ (¬ ((r3_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_2630 r3_kind) (replay_966 r3_kind)
  have n15 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1977 c2_kind) (replay_693 c2_kind)
  have n16 : (shared_expr_Classification163_1 c2_depth h) := by
    exact Iff.mp (normalization_9186 c2_depth h) (replay_12347 c2_depth h)
  have n17 : (shared_expr_Classification163_4 c2_node r2_node) := by
    exact Iff.mp (normalization_9198 c2_node r2_node) (replay_12354 c2_node r2_node)
  have n18 : ((((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_7286 c3_kind) (replay_5108 c3_kind)
  have n19 : (shared_expr_Classification163_5 c3_depth h) := by
    exact Iff.mp (normalization_9208 c3_depth h) (replay_12357 c3_depth h)
  have n20 : ((((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6942 c3_sign) (replay_4980 c3_sign)
  have n21 : (shared_expr_Classification163_8 c3_node r2_node) := by
    exact Iff.mp (normalization_9215 c3_node r2_node) (replay_12360 c3_node r2_node)
  have n22 : (shared_expr_Classification163_18 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node) := by
    exact Iff.mp (normalization_9227 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node) (replay_12361 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node)
  have hn := ht ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22⟩
  exact Iff.mpr (normalization_9229 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) hn

abbrev shared_expr_Classification163_30 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))) ∨ (¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int))) ∨ (¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))) ∨ (¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int))) ∨ (¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ∨ (¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int))) ∨ (¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))) ∨ (¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))))) ∨ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))))))) ∨ (¬ ((¬ (formula_3456 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (formula_3457 c1_depth c1_kind c1_node h r2_node)))))
abbrev formula_3461 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (shared_expr_Classification163_30 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)

abbrev formula_3462 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (¬ (formula_3461 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

abbrev shared_expr_Classification163_31 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((formula_3459 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (formula_3462 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
abbrev formula_3463 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (shared_expr_Classification163_31 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)

theorem normalized_2983 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ ((¬ p4) ∨ (¬ (¬ p5)))) ∧ p6 ∧ (¬ ((¬ p7) ∨ (¬ (¬ p8)))) ∧ (¬ ((¬ (¬ p9)) ∨ (¬ p10))) ∧ (¬ ((¬ (¬ p11)) ∨ (¬ p12))) ∧ (¬ ((¬ (¬ p13)) ∨ (¬ p14))) ∧ (¬ ((¬ p15) ∨ (¬ (¬ p16)))) ∧ (¬ ((¬ p17) ∨ (¬ (¬ p18)))) ∧ (¬ ((¬ p19) ∨ (¬ (¬ p20)))) ∧ (¬ ((¬ p21) ∨ (¬ (¬ p22)))) ∧ (¬ ((¬ p23) ∨ (¬ (¬ p24)))) ∧ (¬ ((¬ p25) ∨ (¬ (¬ p26)))) ∧ (¬ ((¬ p27) ∨ (¬ (¬ p28)))) ∧ (¬ ((¬ p29) ∨ (¬ (¬ p30)))) ∧ (¬ ((¬ p31) ∨ (¬ (¬ p32)))) ∧ (¬ ((¬ (¬ p33)) ∨ (¬ p34))) ∧ (¬ ((¬ p35) ∨ (¬ (¬ p36)))) ∧ (¬ ((¬ (¬ p37)) ∨ (¬ p38))) ∧ (¬ ((¬ p39) ∨ (¬ (¬ p40)))) ∧ (¬ ((¬ (¬ p41)) ∨ (¬ p42))) ∧ p43) ↔ (¬ ((¬ (¬ p8)) ∨ (¬ p25) ∨ (¬ p34) ∨ (¬ (¬ p41)) ∨ (¬ (¬ p18)) ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ (¬ p11)) ∨ (¬ p17) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p19) ∨ (¬ (¬ p20)) ∨ (¬ (¬ p13)) ∨ (¬ p23) ∨ (¬ (¬ p24)) ∨ (¬ (¬ p26)) ∨ (¬ p27) ∨ (¬ (¬ p28)) ∨ (¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p21) ∨ (¬ (¬ p22)) ∨ (¬ p15) ∨ (¬ p29) ∨ (¬ (¬ p30)) ∨ (¬ p31) ∨ (¬ (¬ p32)) ∨ (¬ p35) ∨ (¬ (¬ p36)) ∨ (¬ p39) ∨ (¬ (¬ p40)) ∨ (¬ p7) ∨ (¬ (¬ p9)) ∨ (¬ p10) ∨ (¬ (¬ p33)) ∨ (¬ p42) ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ (¬ p16)) ∨ (¬ (¬ p37)) ∨ (¬ p38) ∨ (¬ p6) ∨ (¬ p43)))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9230 (r0_mode : Int) : (¬ ((¬ ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))))) ∨ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))))))) ↔ (¬ ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∨ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))))))) := (not_congr (normalization_9085 r0_mode))

theorem normalization_9231 (c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node : Int) : (¬ ((¬ (formula_3456 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (formula_3457 c1_depth c1_kind c1_node h r2_node)))) ↔ (¬ ((¬ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node)))) := (not_congr (normalization_9226 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node))

abbrev shared_expr_Classification163_32 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))) ∨ (¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int)))) ∨ (¬ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int)))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∨ (¬ ((r2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r2_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r3_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r3_kind) ≤ (1 : Int)))) ∨ (¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))) ∨ (¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))) ∨ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∨ (¬ ((c3_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (0 : Int)))) ∨ (¬ ((c3_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c3_sign) ≤ (0 : Int)))) ∨ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∨ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)))) ∨ (¬ ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∨ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))))))) ∨ (¬ ((¬ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node)))))
theorem normalization_9232 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3461 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := (or_congr (normalization_6263 r0_mode r1_mode) (or_congr (normalization_434 h r2_depth) (or_congr (normalization_4127 c2_node r2_node) (or_congr (normalization_8424 c3_node r2_node) (or_congr (normalization_961 r0_group) (or_congr (normalization_877 r0_kind) (or_congr (normalization_878 r0_kind) (or_congr (normalization_3749 h r0_level) (or_congr (normalization_959 r0_group) (or_congr (normalization_79 r1_kind) (or_congr (normalization_81 r1_kind) (or_congr (normalization_91 r1_group) (or_congr (normalization_93 r1_group) (or_congr (normalization_83 h r1_level) (or_congr (normalization_425 r2_kind) (or_congr (normalization_427 r2_kind) (or_congr (normalization_428 h r2_depth) (or_congr (normalization_595 r3_kind) (or_congr (normalization_597 r3_kind) (or_congr (normalization_3512 c0_kind) (or_congr (normalization_3513 c0_kind) (or_congr (normalization_5194 c0_group) (or_congr (normalization_5196 c0_group) (or_congr (normalization_5192 c0_level h) (or_congr (normalization_964 c2_kind) (or_congr (normalization_966 c2_kind) (or_congr (normalization_2185 c2_depth h) (or_congr (normalization_2191 c2_depth h) (or_congr (normalization_6811 c3_kind) (or_congr (normalization_6813 c3_kind) (or_congr (normalization_6845 c3_sign) (or_congr (normalization_6847 c3_sign) (or_congr (normalization_6299 r0_mode r1_mode) (or_congr (normalization_9109 c0_mode r0_mode) (or_congr (normalization_9110 c0_mode r0_mode) (or_congr (normalization_4297 c2_node r2_node) (or_congr (normalization_9211 c3_node r2_node) (or_congr (normalization_9124 h r0_level) (or_congr (normalization_9138 h r1_level) (or_congr (normalization_9152 c0_level h) (or_congr (normalization_9203 c3_depth h) (or_congr (normalization_9204 c3_depth h) (or_congr (normalization_9230 r0_mode) (normalization_9231 c1_depth c1_group c1_kind c1_level c1_mode c1_node h r0_mode r2_node))))))))))))))))))))))))))))))))))))))))))))

theorem normalization_9233 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3462 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (¬ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)) := (not_congr (normalization_9232 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

abbrev shared_expr_Classification163_33 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((shared_expr_Classification163_21 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (¬ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)))
theorem normalization_9234 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3463 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_33 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := (iff_congr (normalization_9228 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (normalization_9233 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

-- Checked replay of rewrite.
theorem replay_12363 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3463 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
  classical
  have ht := (normalized_2983 ((r0_kind) ≤ (0 : Int)) ((r0_kind) ≤ (-1 : Int)) ((r1_kind) ≤ (0 : Int)) ((r1_kind) ≤ (-1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_kind) ≤ (-1 : Int)) ((¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))))) ∨ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int)) ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * h)) ≤ (-1 : Int)) ((r0_group) ≤ (1 : Int)) ((r0_group) ≤ (0 : Int)) ((r1_group) ≤ (2 : Int)) ((r1_group) ≤ (1 : Int)) ((c0_group) ≤ (1 : Int)) ((c0_group) ≤ (0 : Int)) ((r2_kind) ≤ (1 : Int)) ((r2_kind) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((r3_kind) ≤ (2 : Int)) ((r3_kind) ≤ (1 : Int)) ((c2_kind) ≤ (1 : Int)) ((c2_kind) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) ((c2_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ((c3_kind) ≤ (1 : Int)) ((c3_kind) ≤ (0 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (-2 : Int)) ((c3_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c3_sign) ≤ (1 : Int)) ((c3_sign) ≤ (0 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((r2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((¬ (shared_expr_Classification163_13 c1_group c1_kind c1_level c1_mode h r0_mode)) ∨ (¬ (shared_expr_Classification163_14 c1_depth c1_kind c1_node h r2_node))))
  have hn := ht
  exact Iff.mpr (normalization_9234 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) hn

abbrev shared_expr_Classification163_34 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((formula_3448 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (formula_3462 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
abbrev formula_3464 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (shared_expr_Classification163_34 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)

theorem normalized_2984 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification163_35 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((shared_expr_Classification163_22 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (¬ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)))
theorem normalization_9235 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3464 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_35 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := (iff_congr (normalization_9078 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (normalization_9233 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

-- Checked replay of trans.
theorem replay_12364 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3464 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
  classical
  have ht := (normalized_2984 (shared_expr_Classification163_22 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (shared_expr_Classification163_21 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
  have n0 : (shared_expr_Classification163_23 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
    exact Iff.mp (normalization_9229 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (replay_12362 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)
  have n1 : (shared_expr_Classification163_33 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
    exact Iff.mp (normalization_9234 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (replay_12363 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9235 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) hn

abbrev formula_3465 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (¬ (formula_3462 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

abbrev shared_expr_Classification163_36 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((formula_3449 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (formula_3465 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
abbrev formula_3466 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (shared_expr_Classification163_36 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)

theorem normalized_2985 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_9236 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3465 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (¬ (¬ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))) := (not_congr (normalization_9233 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

abbrev shared_expr_Classification163_37 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((¬ (shared_expr_Classification163_22 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)) ↔ (¬ (¬ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))))
theorem normalization_9237 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3466 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_37 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := (iff_congr (normalization_9079 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (normalization_9236 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

-- Checked replay of monotonicity.
theorem replay_12365 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3466 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
  classical
  have ht := (normalized_2985 (shared_expr_Classification163_22 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
  have n0 : (shared_expr_Classification163_35 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
    exact Iff.mp (normalization_9235 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (replay_12364 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_9237 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) hn

abbrev shared_expr_Classification163_38 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((formula_3465 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (formula_3461 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
abbrev formula_3467 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (shared_expr_Classification163_38 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)

theorem normalized_2986 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification163_39 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((¬ (¬ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))) ↔ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
theorem normalization_9238 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3467 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_39 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := (iff_congr (normalization_9236 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (normalization_9232 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

-- Checked replay of rewrite.
theorem replay_12366 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3467 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
  classical
  have ht := (normalized_2986 (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
  have hn := ht
  exact Iff.mpr (normalization_9238 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) hn

abbrev shared_expr_Classification163_40 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((formula_3449 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (formula_3461 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
abbrev formula_3468 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := (shared_expr_Classification163_40 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)

theorem normalized_2987 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification163_41 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : Prop := ((¬ (shared_expr_Classification163_22 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)) ↔ (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
theorem normalization_9239 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3468 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) ↔ (shared_expr_Classification163_41 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := (iff_congr (normalization_9079 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (normalization_9232 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))

-- Checked replay of trans.
theorem replay_12367 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) : (formula_3468 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
  classical
  have ht := (normalized_2987 (shared_expr_Classification163_22 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (shared_expr_Classification163_32 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind))
  have n0 : (shared_expr_Classification163_37 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
    exact Iff.mp (normalization_9237 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (replay_12365 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)
  have n1 : (shared_expr_Classification163_39 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
    exact Iff.mp (normalization_9238 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (replay_12366 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_9239 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) hn

-- Checked replay of mp.
theorem replay_12368 (c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind : Int) (i729 : (formula_3441 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind)) : (formula_3461 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) := by
  exact Iff.mp (replay_12367 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind) (replay_12292 c0_group c0_kind c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c2_depth c2_kind c2_node c3_depth c3_kind c3_node c3_sign h r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode r2_depth r2_kind r2_node r3_kind i729)

-- Checked replay of th-lemma.
theorem replay_12369 (r0_mode r1_mode : Int) : ((r0_mode ≤ (4 : Int)) ∨ (r1_mode ≥ (6 : Int)) ∨ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_12370 (r0_mode : Int) : ((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_2988 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p8) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_12371 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_251 c2_depth c2_kind c2_node c2_sign r0_level) ∨ ((c2_node % (2 : Int)) ≤ (0 : Int))) := by
  exact (propositional_2988 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c2_node % (2 : Int)) ≤ (0 : Int)))

abbrev shared_expr_Classification163_42 (c2_node c3_node r2_node : Int) : Prop := ((¬ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≥ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (((2 : Int) * (c2_node / (2 : Int))) + (c2_node % (2 : Int))))) ≤ (0 : Int))) ∨ ((r2_node % (2 : Int)) ≤ (0 : Int)) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node % (2 : Int)) ≤ (0 : Int))))
abbrev formula_3469 (c2_node c3_node r2_node : Int) : Prop := (shared_expr_Classification163_42 c2_node c3_node r2_node)

-- Checked replay of th-lemma.
theorem replay_12372 (c2_node c3_node r2_node : Int) : (formula_3469 c2_node c3_node r2_node) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Classification163_43 (c2_node c3_node : Int) : Prop := (((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ∨ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))
abbrev formula_3470 (c2_node c3_node : Int) : Prop := (shared_expr_Classification163_43 c2_node c3_node)

theorem propositional_2989 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_12373 (c2_node c3_node : Int) : (formula_3470 c2_node c3_node) := by
  exact (propositional_2989 ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))

abbrev shared_expr_Classification163_44 (c2_node c3_node r2_node : Int) : Prop := ((¬ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≥ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (((2 : Int) * (c2_node / (2 : Int))) + (c2_node % (2 : Int))))) ≤ (0 : Int))) ∨ ((r2_node % (2 : Int)) ≤ (0 : Int)) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node % (2 : Int)) ≤ (1 : Int))) ∨ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)))
abbrev formula_3471 (c2_node c3_node r2_node : Int) : Prop := (shared_expr_Classification163_44 c2_node c3_node r2_node)

-- Checked replay of th-lemma.
theorem replay_12374 (c2_node c3_node r2_node : Int) : (formula_3471 c2_node c3_node r2_node) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_12375 (c0_mode r1_mode : Int) : ((r1_mode ≤ (4 : Int)) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ (c0_mode ≤ (4 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_12376 (c2_node c3_node : Int) : (((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) ∨ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Classification163_45 (c2_node c3_node r2_node : Int) : Prop := ((¬ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≥ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (((2 : Int) * (c2_node / (2 : Int))) + (c2_node % (2 : Int))))) ≤ (0 : Int))) ∨ (¬ ((r2_node % (2 : Int)) ≥ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node % (2 : Int)) ≤ (0 : Int))) ∨ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))
abbrev formula_3472 (c2_node c3_node r2_node : Int) : Prop := (shared_expr_Classification163_45 c2_node c3_node r2_node)

-- Checked replay of th-lemma.
theorem replay_12377 (c2_node c3_node r2_node : Int) : (formula_3472 c2_node c3_node r2_node) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_12378 (c2_node c3_node r2_node : Int) (i392 : ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) (i730 : ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) (i731 : ((c2_node % (2 : Int)) ≤ (0 : Int))) : ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) := by
  exact (Or.elim (replay_12377 c2_node c3_node r2_node) (fun l0 => (False.elim (l0 (replay_7620 r2_node)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7626 c2_node)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_7618 r2_node)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i730))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i392))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i731))) (fun t5 => t5))))))))))))

end H4Formal.Generated.Classification
