import H4Formal.Certificates.CheckedRepair.Repair038

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_881 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3487 (r1_mode : Int) : ((r1_mode = (0 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int)))))) ↔ ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))))) := (iff_congr (normalization_2771 r1_mode) (normalization_3485 r1_mode))

-- Checked replay of trans.
theorem replay_2371 (r1_mode : Int) : ((r1_mode = (0 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_881 (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))))))
  have n0 : ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ↔ (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_3483 r1_mode) (replay_2369 r1_mode)
  have n1 : ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3486 r1_mode) (replay_2370 r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3487 r1_mode) hn

theorem normalized_882 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3488 (r1_group : Int) : ((r1_group ≤ (1 : Int)) ∧ (r1_group ≥ (1 : Int))) ↔ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) := (and_congr (normalization_2822 r1_group) (normalization_2824 r1_group))

theorem normalization_3489 (r1_group : Int) : ((r1_group = (1 : Int)) ↔ ((r1_group ≤ (1 : Int)) ∧ (r1_group ≥ (1 : Int)))) ↔ ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) := (iff_congr (normalization_2761 r1_group) (normalization_3488 r1_group))

-- Checked replay of rewrite.
theorem replay_2372 (r1_group : Int) : ((r1_group = (1 : Int)) ↔ ((r1_group ≤ (1 : Int)) ∧ (r1_group ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_882 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3489 r1_group) hn

theorem normalized_883 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3490 (r1_group : Int) : (((r1_group ≤ (1 : Int)) ∧ (r1_group ≥ (1 : Int))) ↔ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ↔ ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := (iff_congr (normalization_3488 r1_group) (normalization_2827 r1_group))

-- Checked replay of rewrite.
theorem replay_2373 (r1_group : Int) : (((r1_group ≤ (1 : Int)) ∧ (r1_group ≥ (1 : Int))) ↔ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_883 ((r1_group) ≤ (1 : Int)) ((r1_group) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3490 r1_group) hn

theorem normalized_884 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3491 (r1_group : Int) : ((r1_group = (1 : Int)) ↔ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ↔ ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := (iff_congr (normalization_2761 r1_group) (normalization_2827 r1_group))

-- Checked replay of trans.
theorem replay_2374 (r1_group : Int) : ((r1_group = (1 : Int)) ↔ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_884 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_3489 r1_group) (replay_2372 r1_group)
  have n1 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3490 r1_group) (replay_2373 r1_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3491 r1_group) hn

theorem normalized_885 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3492 (c0_kind : Int) : ((c0_kind ≤ (1 : Int)) ∧ (c0_kind ≥ (1 : Int))) ↔ (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) := (and_congr (normalization_452 c0_kind) (normalization_454 c0_kind))

theorem normalization_3493 (c0_kind : Int) : ((c0_kind = (1 : Int)) ↔ ((c0_kind ≤ (1 : Int)) ∧ (c0_kind ≥ (1 : Int)))) ↔ ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int))))) := (iff_congr (normalization_142 c0_kind) (normalization_3492 c0_kind))

-- Checked replay of rewrite.
theorem replay_2375 (c0_kind : Int) : ((c0_kind = (1 : Int)) ↔ ((c0_kind ≤ (1 : Int)) ∧ (c0_kind ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_885 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3493 c0_kind) hn

theorem normalized_886 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3494 (c0_kind : Int) : ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int)))) ↔ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))) := (or_congr (normalization_453 c0_kind) (normalization_455 c0_kind))

theorem normalization_3495 (c0_kind : Int) : (¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))))) := (not_congr (normalization_3494 c0_kind))

theorem normalization_3496 (c0_kind : Int) : (((c0_kind ≤ (1 : Int)) ∧ (c0_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int)))))) ↔ ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_3492 c0_kind) (normalization_3495 c0_kind))

-- Checked replay of rewrite.
theorem replay_2376 (c0_kind : Int) : (((c0_kind ≤ (1 : Int)) ∧ (c0_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_886 ((c0_kind) ≤ (1 : Int)) ((c0_kind) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3496 c0_kind) hn

theorem normalized_887 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3497 (c0_kind : Int) : ((c0_kind = (1 : Int)) ↔ (¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int)))))) ↔ ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_142 c0_kind) (normalization_3495 c0_kind))

-- Checked replay of trans.
theorem replay_2377 (c0_kind : Int) : ((c0_kind = (1 : Int)) ↔ (¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_887 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))))
  have n0 : ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_3493 c0_kind) (replay_2375 c0_kind)
  have n1 : ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3496 c0_kind) (replay_2376 c0_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3497 c0_kind) hn

theorem normalized_888 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3498 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_3499 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_3500 (c0_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := (and_congr (normalization_3498 c0_depth r1_level) (normalization_3499 c0_depth r1_level))

abbrev shared_expr_Repair039_0 (c0_depth r1_level : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_3501 (c0_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ (((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Repair039_0 c0_depth r1_level) := (iff_congr (normalization_3375 c0_depth r1_level) (normalization_3500 c0_depth r1_level))

-- Checked replay of rewrite.
theorem replay_2378 (c0_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ (((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_888 ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3501 c0_depth r1_level) hn

abbrev shared_expr_Repair039_1 (c0_depth r1_level : Int) : Prop := ((((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))))))
abbrev formula_962 (c0_depth r1_level : Int) : Prop := (shared_expr_Repair039_1 c0_depth r1_level)

theorem normalized_889 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3502 (c0_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) := (not_congr (normalization_3498 c0_depth r1_level))

theorem normalization_3503 (c0_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := (not_congr (normalization_3499 c0_depth r1_level))

theorem normalization_3504 (c0_depth r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (or_congr (normalization_3502 c0_depth r1_level) (normalization_3503 c0_depth r1_level))

theorem normalization_3505 (c0_depth r1_level : Int) : (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) := (not_congr (normalization_3504 c0_depth r1_level))

abbrev shared_expr_Repair039_2 (c0_depth r1_level : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))))
theorem normalization_3506 (c0_depth r1_level : Int) : (formula_962 c0_depth r1_level) ↔ (shared_expr_Repair039_2 c0_depth r1_level) := (iff_congr (normalization_3500 c0_depth r1_level) (normalization_3505 c0_depth r1_level))

-- Checked replay of rewrite.
theorem replay_2379 (c0_depth r1_level : Int) : (formula_962 c0_depth r1_level) := by
  classical
  have ht := (normalized_889 ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3506 c0_depth r1_level) hn

theorem normalized_890 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3507 (c0_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Repair039_2 c0_depth r1_level) := (iff_congr (normalization_3375 c0_depth r1_level) (normalization_3505 c0_depth r1_level))

-- Checked replay of trans.
theorem replay_2380 (c0_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_890 ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) (shared_expr_Repair039_2 c0_depth r1_level))
  have n0 : (shared_expr_Repair039_0 c0_depth r1_level) := by
    exact Iff.mp (normalization_3501 c0_depth r1_level) (replay_2378 c0_depth r1_level)
  have n1 : (shared_expr_Repair039_2 c0_depth r1_level) := by
    exact Iff.mp (normalization_3506 c0_depth r1_level) (replay_2379 c0_depth r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3507 c0_depth r1_level) hn

theorem normalized_891 (p0 p1 p2 p3 : Prop) : (((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_3 (c0_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
theorem normalization_3508 (c0_sign : Int) : (((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int))))))) ↔ (shared_expr_Repair039_3 c0_sign) := (iff_congr (normalization_146 c0_sign) (normalization_468 c0_sign))

-- Checked replay of rewrite.
theorem replay_2381 (c0_sign : Int) : (((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_891 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c0_sign) ≤ (2 : Int)) ((c0_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3508 c0_sign) hn

abbrev shared_expr_Repair039_4 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))))) ∧ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))))
abbrev formula_963 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := (shared_expr_Repair039_4 c0_depth c0_kind c0_sign r1_level)

theorem normalized_892 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → ((p0 ∧ p2 ∧ p4) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_5 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
theorem normalization_3509 (c0_depth c0_kind c0_sign r1_level : Int) : (formula_963 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Repair039_5 c0_depth c0_kind c0_sign r1_level) := (and_congr (normalization_3495 c0_kind) (and_congr (normalization_3505 c0_depth r1_level) (normalization_468 c0_sign)))

abbrev shared_expr_Repair039_6 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
theorem normalization_3510 (c0_depth c0_kind c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (formula_963 c0_depth c0_kind c0_sign r1_level)) ↔ ((shared_expr_Repair039_6 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Repair039_5 c0_depth c0_kind c0_sign r1_level)) := (iff_congr (normalization_3376 c0_depth c0_kind c0_sign r1_level) (normalization_3509 c0_depth c0_kind c0_sign r1_level))

-- Checked replay of monotonicity.
theorem replay_2382 (c0_depth c0_kind c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (formula_963 c0_depth c0_kind c0_sign r1_level)) := by
  classical
  have ht := (normalized_892 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))) ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
  have n0 : ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3497 c0_kind) (replay_2377 c0_kind)
  have n1 : (shared_expr_Repair039_2 c0_depth r1_level) := by
    exact Iff.mp (normalization_3507 c0_depth r1_level) (replay_2380 c0_depth r1_level)
  have n2 : (shared_expr_Repair039_3 c0_sign) := by
    exact Iff.mp (normalization_3508 c0_sign) (replay_2381 c0_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3510 c0_depth c0_kind c0_sign r1_level) hn

theorem normalized_893 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ (¬ p2)) ∨ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_7 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_3511 (c0_depth c0_kind c0_sign r1_level : Int) : (formula_877 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level) := (or_congr (normalization_453 c0_kind) (or_congr (normalization_455 c0_kind) (or_congr (normalization_469 c0_sign) (or_congr (normalization_3502 c0_depth r1_level) (normalization_3503 c0_depth r1_level)))))

theorem normalization_3512 (c0_depth c0_kind c0_sign r1_level : Int) : (¬ (formula_877 c0_depth c0_kind c0_sign r1_level)) ↔ (¬ (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level)) := (not_congr (normalization_3511 c0_depth c0_kind c0_sign r1_level))

theorem normalization_3513 (c0_depth c0_kind c0_sign r1_level : Int) : ((formula_963 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (formula_877 c0_depth c0_kind c0_sign r1_level))) ↔ ((shared_expr_Repair039_5 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))) := (iff_congr (normalization_3509 c0_depth c0_kind c0_sign r1_level) (normalization_3512 c0_depth c0_kind c0_sign r1_level))

-- Checked replay of rewrite.
theorem replay_2383 (c0_depth c0_kind c0_sign r1_level : Int) : ((formula_963 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (formula_877 c0_depth c0_kind c0_sign r1_level))) := by
  classical
  have ht := (normalized_893 ((c0_kind) ≤ (1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
  have hn := ht
  exact Iff.mpr (normalization_3513 c0_depth c0_kind c0_sign r1_level) hn

theorem normalized_894 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3514 (c0_depth c0_kind c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (¬ (formula_877 c0_depth c0_kind c0_sign r1_level))) ↔ ((shared_expr_Repair039_6 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))) := (iff_congr (normalization_3376 c0_depth c0_kind c0_sign r1_level) (normalization_3512 c0_depth c0_kind c0_sign r1_level))

-- Checked replay of trans.
theorem replay_2384 (c0_depth c0_kind c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (0 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (¬ (formula_877 c0_depth c0_kind c0_sign r1_level))) := by
  classical
  have ht := (normalized_894 (shared_expr_Repair039_6 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair039_5 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))
  have n0 : ((shared_expr_Repair039_6 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Repair039_5 c0_depth c0_kind c0_sign r1_level)) := by
    exact Iff.mp (normalization_3510 c0_depth c0_kind c0_sign r1_level) (replay_2382 c0_depth c0_kind c0_sign r1_level)
  have n1 : ((shared_expr_Repair039_5 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))) := by
    exact Iff.mp (normalization_3513 c0_depth c0_kind c0_sign r1_level) (replay_2383 c0_depth c0_kind c0_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3514 c0_depth c0_kind c0_sign r1_level) hn

abbrev shared_expr_Repair039_8 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_877 c0_depth c0_kind c0_sign r1_level))))
abbrev formula_964 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair039_8 c0_depth c0_kind c0_sign r1_group r1_level)

theorem normalized_895 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_9 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))))
theorem normalization_3515 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (formula_964 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_9 c0_depth c0_kind c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_481 c0_kind)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_3512 c0_depth c0_kind c0_sign r1_level)))

abbrev shared_expr_Repair039_10 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair039_6 c0_depth c0_kind c0_sign r1_level)))
theorem normalization_3516 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_940 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_964 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_9 c0_depth c0_kind c0_sign r1_group r1_level)) := (iff_congr (normalization_3377 c0_depth c0_kind c0_sign r1_group r1_level) (normalization_3515 c0_depth c0_kind c0_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_2385 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_940 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_964 c0_depth c0_kind c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_895 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) (shared_expr_Repair039_6 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3067 c0_kind) (replay_2151 c0_kind)
  have n2 : ((shared_expr_Repair039_6 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))) := by
    exact Iff.mp (normalization_3514 c0_depth c0_kind c0_sign r1_level) (replay_2384 c0_depth c0_kind c0_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3516 c0_depth c0_kind c0_sign r1_group r1_level) hn

theorem normalized_896 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_11 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))))
theorem normalization_3517 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (formula_878 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_3512 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_481 c0_kind)))

theorem normalization_3518 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_964 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair039_9 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)) := (iff_congr (normalization_3515 c0_depth c0_kind c0_sign r1_group r1_level) (normalization_3517 c0_depth c0_kind c0_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_2386 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_964 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_896 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) (shared_expr_Repair039_7 c0_depth c0_kind c0_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3518 c0_depth c0_kind c0_sign r1_group r1_level) hn

theorem normalized_897 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3519 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_940 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)) := (iff_congr (normalization_3377 c0_depth c0_kind c0_sign r1_group r1_level) (normalization_3517 c0_depth c0_kind c0_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_2387 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_940 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_897 (shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level) (shared_expr_Repair039_9 c0_depth c0_kind c0_sign r1_group r1_level) (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_9 c0_depth c0_kind c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3516 c0_depth c0_kind c0_sign r1_group r1_level) (replay_2385 c0_depth c0_kind c0_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair039_9 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3518 c0_depth c0_kind c0_sign r1_group r1_level) (replay_2386 c0_depth c0_kind c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3519 c0_depth c0_kind c0_sign r1_group r1_level) hn

abbrev shared_expr_Repair039_12 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (0 : Int)) ∧ (formula_940 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))))) ∧ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))
abbrev formula_965 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair039_12 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)

theorem normalized_898 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3520 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))))) ∧ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)) := (and_congr (normalization_3485 r1_mode) (normalization_3517 c0_depth c0_kind c0_sign r1_group r1_level))

abbrev shared_expr_Repair039_13 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)))
theorem normalization_3521 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_965 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair039_13 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3378 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (normalization_3520 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_2388 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_965 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_898 (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))) (shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level) (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3487 r1_mode) (replay_2371 r1_mode)
  have n1 : ((shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3519 c0_depth c0_kind c0_sign r1_group r1_level) (replay_2387 c0_depth c0_kind c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3521 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair039_14 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))))) ∧ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))))
abbrev formula_966 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair039_14 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)

theorem normalized_899 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ (¬ p1)) ∨ (¬ p0) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3522 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)) := (not_congr (normalization_3517 c0_depth c0_kind c0_sign r1_group r1_level))

theorem normalization_3523 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level))) ↔ ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level))) := (or_congr (normalization_2807 r1_mode) (or_congr (normalization_2809 r1_mode) (normalization_3522 c0_depth c0_kind c0_sign r1_group r1_level)))

theorem normalization_3524 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) ↔ (¬ ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)))) := (not_congr (normalization_3523 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

abbrev shared_expr_Repair039_15 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)))))
theorem normalization_3525 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_966 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair039_15 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3520 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (normalization_3524 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_2389 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_966 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_899 ((r1_mode) ≤ (0 : Int)) ((r1_mode) ≤ (-1 : Int)) (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3525 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair039_16 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (0 : Int)) ∧ (formula_940 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))))
abbrev formula_967 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair039_16 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)

theorem normalized_900 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_17 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)))))
theorem normalization_3526 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_967 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair039_17 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3378 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (normalization_3524 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_2390 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_967 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_900 ((((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair039_10 c0_depth c0_kind c0_sign r1_group r1_level)) ((¬ ((¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level)) ((¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair039_11 c0_depth c0_kind c0_sign r1_group r1_level))))
  have n0 : (shared_expr_Repair039_13 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3521 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (replay_2388 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Repair039_15 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3525 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (replay_2389 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3526 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) hn

theorem normalized_901 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3527 (r1_mode : Int) : (r1_mode ≤ (1 : Int)) ↔ ((r1_mode) ≤ (1 : Int)) := by
  omega

theorem normalization_3528 (r1_mode : Int) : (r1_mode ≥ (1 : Int)) ↔ (¬ ((r1_mode) ≤ (0 : Int))) := by
  omega

theorem normalization_3529 (r1_mode : Int) : ((r1_mode ≤ (1 : Int)) ∧ (r1_mode ≥ (1 : Int))) ↔ (((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) := (and_congr (normalization_3527 r1_mode) (normalization_3528 r1_mode))

theorem normalization_3530 (r1_mode : Int) : ((r1_mode = (1 : Int)) ↔ ((r1_mode ≤ (1 : Int)) ∧ (r1_mode ≥ (1 : Int)))) ↔ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ↔ (((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int))))) := (iff_congr (normalization_3230 r1_mode) (normalization_3529 r1_mode))

-- Checked replay of rewrite.
theorem replay_2391 (r1_mode : Int) : ((r1_mode = (1 : Int)) ↔ ((r1_mode ≤ (1 : Int)) ∧ (r1_mode ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_901 (((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3530 r1_mode) hn

theorem normalized_902 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3531 (r1_mode : Int) : (¬ (r1_mode ≤ (1 : Int))) ↔ (¬ ((r1_mode) ≤ (1 : Int))) := (not_congr (normalization_3527 r1_mode))

theorem normalization_3532 (r1_mode : Int) : (¬ (r1_mode ≥ (1 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) := (not_congr (normalization_3528 r1_mode))

theorem normalization_3533 (r1_mode : Int) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int)))) ↔ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))) := (or_congr (normalization_3531 r1_mode) (normalization_3532 r1_mode))

theorem normalization_3534 (r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) := (not_congr (normalization_3533 r1_mode))

theorem normalization_3535 (r1_mode : Int) : (((r1_mode ≤ (1 : Int)) ∧ (r1_mode ≥ (1 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int)))))) ↔ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))))) := (iff_congr (normalization_3529 r1_mode) (normalization_3534 r1_mode))

-- Checked replay of rewrite.
theorem replay_2392 (r1_mode : Int) : (((r1_mode ≤ (1 : Int)) ∧ (r1_mode ≥ (1 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_902 ((r1_mode) ≤ (1 : Int)) ((r1_mode) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3535 r1_mode) hn

theorem normalized_903 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3536 (r1_mode : Int) : ((r1_mode = (1 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int)))))) ↔ ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))))) := (iff_congr (normalization_3230 r1_mode) (normalization_3534 r1_mode))

-- Checked replay of trans.
theorem replay_2393 (r1_mode : Int) : ((r1_mode = (1 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_903 (((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))))))
  have n0 : ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ↔ (((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_3530 r1_mode) (replay_2391 r1_mode)
  have n1 : ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3535 r1_mode) (replay_2392 r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3536 r1_mode) hn

theorem normalized_904 (p0 p1 p2 : Prop) : (((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p0))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p0)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_18 (c0_sign : Int) : Prop := (((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
theorem normalization_3537 (c0_sign : Int) : (((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int))))))) ↔ (shared_expr_Repair039_18 c0_sign) := (iff_congr (normalization_152 c0_sign) (normalization_496 c0_sign))

-- Checked replay of rewrite.
theorem replay_2394 (c0_sign : Int) : (((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_904 ((c0_sign) ≤ (1 : Int)) ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3537 c0_sign) hn

abbrev shared_expr_Repair039_19 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((¬ (c0_kind ≤ (1 : Int))) ∨ (¬ (c0_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))))) ∧ ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))))
abbrev formula_968 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := (shared_expr_Repair039_19 c0_depth c0_kind c0_sign r1_level)

theorem normalized_905 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → ((p0 ∧ p2 ∧ p4) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_20 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
theorem normalization_3538 (c0_depth c0_kind c0_sign r1_level : Int) : (formula_968 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Repair039_20 c0_depth c0_kind c0_sign r1_level) := (and_congr (normalization_3495 c0_kind) (and_congr (normalization_3505 c0_depth r1_level) (normalization_496 c0_sign)))

abbrev shared_expr_Repair039_21 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))))
theorem normalization_3539 (c0_depth c0_kind c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (formula_968 c0_depth c0_kind c0_sign r1_level)) ↔ ((shared_expr_Repair039_21 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Repair039_20 c0_depth c0_kind c0_sign r1_level)) := (iff_congr (normalization_3379 c0_depth c0_kind c0_sign r1_level) (normalization_3538 c0_depth c0_kind c0_sign r1_level))

-- Checked replay of monotonicity.
theorem replay_2395 (c0_depth c0_kind c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (formula_968 c0_depth c0_kind c0_sign r1_level)) := by
  classical
  have ht := (normalized_905 (((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))) ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
  have n0 : ((((c0_kind) ≤ (1 : Int)) ∧ (¬ ((c0_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3497 c0_kind) (replay_2377 c0_kind)
  have n1 : (shared_expr_Repair039_2 c0_depth r1_level) := by
    exact Iff.mp (normalization_3507 c0_depth r1_level) (replay_2380 c0_depth r1_level)
  have n2 : (shared_expr_Repair039_18 c0_sign) := by
    exact Iff.mp (normalization_3537 c0_sign) (replay_2394 c0_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3539 c0_depth c0_kind c0_sign r1_level) hn

theorem normalized_906 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ (¬ p2)) ∨ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_22 (c0_depth c0_kind c0_sign r1_level : Int) : Prop := ((¬ ((c0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))
theorem normalization_3540 (c0_depth c0_kind c0_sign r1_level : Int) : (formula_879 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level) := (or_congr (normalization_453 c0_kind) (or_congr (normalization_455 c0_kind) (or_congr (normalization_497 c0_sign) (or_congr (normalization_3502 c0_depth r1_level) (normalization_3503 c0_depth r1_level)))))

theorem normalization_3541 (c0_depth c0_kind c0_sign r1_level : Int) : (¬ (formula_879 c0_depth c0_kind c0_sign r1_level)) ↔ (¬ (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level)) := (not_congr (normalization_3540 c0_depth c0_kind c0_sign r1_level))

theorem normalization_3542 (c0_depth c0_kind c0_sign r1_level : Int) : ((formula_968 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (formula_879 c0_depth c0_kind c0_sign r1_level))) ↔ ((shared_expr_Repair039_20 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))) := (iff_congr (normalization_3538 c0_depth c0_kind c0_sign r1_level) (normalization_3541 c0_depth c0_kind c0_sign r1_level))

-- Checked replay of rewrite.
theorem replay_2396 (c0_depth c0_kind c0_sign r1_level : Int) : ((formula_968 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (formula_879 c0_depth c0_kind c0_sign r1_level))) := by
  classical
  have ht := (normalized_906 ((c0_kind) ≤ (1 : Int)) ((c0_kind) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-2 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))))
  have hn := ht
  exact Iff.mpr (normalization_3542 c0_depth c0_kind c0_sign r1_level) hn

theorem normalized_907 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3543 (c0_depth c0_kind c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (¬ (formula_879 c0_depth c0_kind c0_sign r1_level))) ↔ ((shared_expr_Repair039_21 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))) := (iff_congr (normalization_3379 c0_depth c0_kind c0_sign r1_level) (normalization_3541 c0_depth c0_kind c0_sign r1_level))

-- Checked replay of trans.
theorem replay_2397 (c0_depth c0_kind c0_sign r1_level : Int) : (((c0_kind = (1 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ ((c0_sign = (1 : Int)) ∨ (c0_sign = (2 : Int)))) ↔ (¬ (formula_879 c0_depth c0_kind c0_sign r1_level))) := by
  classical
  have ht := (normalized_907 (shared_expr_Repair039_21 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair039_20 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))
  have n0 : ((shared_expr_Repair039_21 c0_depth c0_kind c0_sign r1_level) ↔ (shared_expr_Repair039_20 c0_depth c0_kind c0_sign r1_level)) := by
    exact Iff.mp (normalization_3539 c0_depth c0_kind c0_sign r1_level) (replay_2395 c0_depth c0_kind c0_sign r1_level)
  have n1 : ((shared_expr_Repair039_20 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))) := by
    exact Iff.mp (normalization_3542 c0_depth c0_kind c0_sign r1_level) (replay_2396 c0_depth c0_kind c0_sign r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3543 c0_depth c0_kind c0_sign r1_level) hn

abbrev shared_expr_Repair039_23 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) ∨ ((¬ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))))) ∧ (¬ (formula_879 c0_depth c0_kind c0_sign r1_level))))
abbrev formula_969 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair039_23 c0_depth c0_kind c0_sign r1_group r1_level)

theorem normalized_908 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_24 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))))
theorem normalization_3544 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (formula_969 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_24 c0_depth c0_kind c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2827 r1_group) (normalization_481 c0_kind)) (and_congr (not_congr (normalization_2827 r1_group)) (normalization_3541 c0_depth c0_kind c0_sign r1_level)))

abbrev shared_expr_Repair039_25 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := (((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∧ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∨ ((¬ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair039_21 c0_depth c0_kind c0_sign r1_level)))
theorem normalization_3545 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_941 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_969 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_24 c0_depth c0_kind c0_sign r1_group r1_level)) := (iff_congr (normalization_3380 c0_depth c0_kind c0_sign r1_group r1_level) (normalization_3544 c0_depth c0_kind c0_sign r1_group r1_level))

-- Checked replay of monotonicity.
theorem replay_2398 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_941 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_969 c0_depth c0_kind c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_908 (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) (shared_expr_Repair039_21 c0_depth c0_kind c0_sign r1_level) (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))
  have n0 : ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3491 r1_group) (replay_2374 r1_group)
  have n1 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3067 c0_kind) (replay_2151 c0_kind)
  have n2 : ((shared_expr_Repair039_21 c0_depth c0_kind c0_sign r1_level) ↔ (¬ (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))) := by
    exact Iff.mp (normalization_3543 c0_depth c0_kind c0_sign r1_level) (replay_2397 c0_depth c0_kind c0_sign r1_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_3545 c0_depth c0_kind c0_sign r1_group r1_level) hn

theorem normalized_909 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_26 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : Prop := ((((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))) ∨ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))))
theorem normalization_3546 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (formula_880 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level) := (or_congr (and_congr (normalization_2826 r1_group) (normalization_3541 c0_depth c0_kind c0_sign r1_level)) (and_congr (not_congr (normalization_2826 r1_group)) (normalization_481 c0_kind)))

theorem normalization_3547 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_969 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair039_24 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)) := (iff_congr (normalization_3544 c0_depth c0_kind c0_sign r1_group r1_level) (normalization_3546 c0_depth c0_kind c0_sign r1_group r1_level))

-- Checked replay of rewrite.
theorem replay_2399 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_969 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_909 ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) (shared_expr_Repair039_22 c0_depth c0_kind c0_sign r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3547 c0_depth c0_kind c0_sign r1_group r1_level) hn

theorem normalized_910 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3548 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_941 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)) := (iff_congr (normalization_3380 c0_depth c0_kind c0_sign r1_group r1_level) (normalization_3546 c0_depth c0_kind c0_sign r1_group r1_level))

-- Checked replay of trans.
theorem replay_2400 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((formula_941 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) := by
  classical
  have ht := (normalized_910 (shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level) (shared_expr_Repair039_24 c0_depth c0_kind c0_sign r1_group r1_level) (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level))
  have n0 : ((shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_24 c0_depth c0_kind c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3545 c0_depth c0_kind c0_sign r1_group r1_level) (replay_2398 c0_depth c0_kind c0_sign r1_group r1_level)
  have n1 : ((shared_expr_Repair039_24 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3547 c0_depth c0_kind c0_sign r1_group r1_level) (replay_2399 c0_depth c0_kind c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3548 c0_depth c0_kind c0_sign r1_group r1_level) hn

abbrev shared_expr_Repair039_27 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (1 : Int)) ∧ (formula_941 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))))) ∧ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))
abbrev formula_970 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair039_27 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)

theorem normalized_911 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3549 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : ((¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))))) ∧ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)) := (and_congr (normalization_3534 r1_mode) (normalization_3546 c0_depth c0_kind c0_sign r1_group r1_level))

abbrev shared_expr_Repair039_28 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ ((¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)))
theorem normalization_3550 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_970 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair039_28 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3381 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (normalization_3549 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

-- Checked replay of monotonicity.
theorem replay_2401 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_970 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_911 (((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))) (shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level) (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level))
  have n0 : ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3536 r1_mode) (replay_2393 r1_mode)
  have n1 : ((shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level) ↔ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)) := by
    exact Iff.mp (normalization_3548 c0_depth c0_kind c0_sign r1_group r1_level) (replay_2400 c0_depth c0_kind c0_sign r1_group r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3550 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair039_29 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))))) ∧ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))))
abbrev formula_971 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair039_29 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)

theorem normalized_912 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3551 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)) := (not_congr (normalization_3546 c0_depth c0_kind c0_sign r1_group r1_level))

theorem normalization_3552 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level))) ↔ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level))) := (or_congr (normalization_3531 r1_mode) (or_congr (normalization_3532 r1_mode) (normalization_3551 c0_depth c0_kind c0_sign r1_group r1_level)))

theorem normalization_3553 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)))) := (not_congr (normalization_3552 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

abbrev shared_expr_Repair039_30 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)))))
theorem normalization_3554 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_971 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair039_30 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3549 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (normalization_3553 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

-- Checked replay of rewrite.
theorem replay_2402 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_971 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_912 ((r1_mode) ≤ (1 : Int)) ((r1_mode) ≤ (0 : Int)) (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level))
  have hn := ht
  exact Iff.mpr (normalization_3554 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) hn

abbrev shared_expr_Repair039_31 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((r1_mode = (1 : Int)) ∧ (formula_941 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))))
abbrev formula_972 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair039_31 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)

theorem normalized_913 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_32 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : Prop := (((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level)) ↔ (¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)))))
theorem normalization_3555 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_972 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) ↔ (shared_expr_Repair039_32 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := (iff_congr (normalization_3381 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (normalization_3553 c0_depth c0_kind c0_sign r1_group r1_level r1_mode))

-- Checked replay of trans.
theorem replay_2403 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (formula_972 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
  classical
  have ht := (normalized_913 ((((r1_mode) ≤ (1 : Int)) ∧ (¬ ((r1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair039_25 c0_depth c0_kind c0_sign r1_group r1_level)) ((¬ ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))))) ∧ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level)) ((¬ ((r1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair039_26 c0_depth c0_kind c0_sign r1_group r1_level))))
  have n0 : (shared_expr_Repair039_28 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3550 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (replay_2401 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)
  have n1 : (shared_expr_Repair039_30 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) := by
    exact Iff.mp (normalization_3554 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) (replay_2402 c0_depth c0_kind c0_sign r1_group r1_level r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3555 c0_depth c0_kind c0_sign r1_group r1_level r1_mode) hn

theorem normalized_914 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3556 (r1_mode : Int) : (r1_mode ≤ (2 : Int)) ↔ ((r1_mode) ≤ (2 : Int)) := by
  omega

theorem normalization_3557 (r1_mode : Int) : (r1_mode ≥ (2 : Int)) ↔ (¬ ((r1_mode) ≤ (1 : Int))) := by
  omega

theorem normalization_3558 (r1_mode : Int) : ((r1_mode ≤ (2 : Int)) ∧ (r1_mode ≥ (2 : Int))) ↔ (((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) := (and_congr (normalization_3556 r1_mode) (normalization_3557 r1_mode))

theorem normalization_3559 (r1_mode : Int) : ((r1_mode = (2 : Int)) ↔ ((r1_mode ≤ (2 : Int)) ∧ (r1_mode ≥ (2 : Int)))) ↔ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ↔ (((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int))))) := (iff_congr (normalization_3234 r1_mode) (normalization_3558 r1_mode))

-- Checked replay of rewrite.
theorem replay_2404 (r1_mode : Int) : ((r1_mode = (2 : Int)) ↔ ((r1_mode ≤ (2 : Int)) ∧ (r1_mode ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_914 (((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3559 r1_mode) hn

theorem normalized_915 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3560 (r1_mode : Int) : (¬ (r1_mode ≤ (2 : Int))) ↔ (¬ ((r1_mode) ≤ (2 : Int))) := (not_congr (normalization_3556 r1_mode))

theorem normalization_3561 (r1_mode : Int) : (¬ (r1_mode ≥ (2 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (1 : Int)))) := (not_congr (normalization_3557 r1_mode))

theorem normalization_3562 (r1_mode : Int) : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int)))) ↔ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))) := (or_congr (normalization_3560 r1_mode) (normalization_3561 r1_mode))

theorem normalization_3563 (r1_mode : Int) : (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int)))))) := (not_congr (normalization_3562 r1_mode))

theorem normalization_3564 (r1_mode : Int) : (((r1_mode ≤ (2 : Int)) ∧ (r1_mode ≥ (2 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int)))))) ↔ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))))) := (iff_congr (normalization_3558 r1_mode) (normalization_3563 r1_mode))

-- Checked replay of rewrite.
theorem replay_2405 (r1_mode : Int) : (((r1_mode ≤ (2 : Int)) ∧ (r1_mode ≥ (2 : Int))) ↔ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_915 ((r1_mode) ≤ (2 : Int)) ((r1_mode) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3564 r1_mode) hn

theorem normalized_916 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3565 (r1_mode : Int) : ((r1_mode = (2 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int)))))) ↔ ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))))) := (iff_congr (normalization_3234 r1_mode) (normalization_3563 r1_mode))

-- Checked replay of trans.
theorem replay_2406 (r1_mode : Int) : ((r1_mode = (2 : Int)) ↔ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_916 (((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))))))
  have n0 : ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ↔ (((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_3559 r1_mode) (replay_2404 r1_mode)
  have n1 : ((((r1_mode) ≤ (2 : Int)) ∧ (¬ ((r1_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3564 r1_mode) (replay_2405 r1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3565 r1_mode) hn

theorem normalized_917 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3566 (c0_depth r1_level : Int) : (c0_depth ≤ r1_level) ↔ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_3567 (c0_depth r1_level : Int) : (c0_depth ≥ r1_level) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3568 (c0_depth r1_level : Int) : ((c0_depth ≤ r1_level) ∧ (c0_depth ≥ r1_level)) ↔ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (and_congr (normalization_3566 c0_depth r1_level) (normalization_3567 c0_depth r1_level))

abbrev shared_expr_Repair039_33 (c0_depth r1_level : Int) : Prop := ((((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ↔ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_3569 (c0_depth r1_level : Int) : ((c0_depth = r1_level) ↔ ((c0_depth ≤ r1_level) ∧ (c0_depth ≥ r1_level))) ↔ (shared_expr_Repair039_33 c0_depth r1_level) := (iff_congr (normalization_3235 c0_depth r1_level) (normalization_3568 c0_depth r1_level))

-- Checked replay of rewrite.
theorem replay_2407 (c0_depth r1_level : Int) : ((c0_depth = r1_level) ↔ ((c0_depth ≤ r1_level) ∧ (c0_depth ≥ r1_level))) := by
  classical
  have ht := (normalized_917 (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3569 c0_depth r1_level) hn

theorem normalized_918 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3570 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_3571 (c0_depth r1_level : Int) : ((c0_depth ≤ r1_level) ↔ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (iff_congr (normalization_3566 c0_depth r1_level) (normalization_3570 c0_depth r1_level))

-- Checked replay of rewrite.
theorem replay_2408 (c0_depth r1_level : Int) : ((c0_depth ≤ r1_level) ↔ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_918 ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3571 c0_depth r1_level) hn

theorem normalized_919 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3572 (c0_depth r1_level : Int) : ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3573 (c0_depth r1_level : Int) : ((c0_depth ≥ r1_level) ↔ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_3567 c0_depth r1_level) (normalization_3572 c0_depth r1_level))

-- Checked replay of rewrite.
theorem replay_2409 (c0_depth r1_level : Int) : ((c0_depth ≥ r1_level) ↔ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_919 ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3573 c0_depth r1_level) hn

theorem normalized_920 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3574 (c0_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (and_congr (normalization_3570 c0_depth r1_level) (normalization_3572 c0_depth r1_level))

theorem normalization_3575 (c0_depth r1_level : Int) : (((c0_depth ≤ r1_level) ∧ (c0_depth ≥ r1_level)) ↔ (((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))) ↔ (shared_expr_Repair039_33 c0_depth r1_level) := (iff_congr (normalization_3568 c0_depth r1_level) (normalization_3574 c0_depth r1_level))

-- Checked replay of monotonicity.
theorem replay_2410 (c0_depth r1_level : Int) : (((c0_depth ≤ r1_level) ∧ (c0_depth ≥ r1_level)) ↔ (((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))) := by
  classical
  have ht := (normalized_920 ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
  have n0 : (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_3571 c0_depth r1_level) (replay_2408 c0_depth r1_level)
  have n1 : ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3573 c0_depth r1_level) (replay_2409 c0_depth r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3575 c0_depth r1_level) hn

abbrev shared_expr_Repair039_34 (c0_depth r1_level : Int) : Prop := ((((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ∧ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))))))
abbrev formula_973 (c0_depth r1_level : Int) : Prop := (shared_expr_Repair039_34 c0_depth r1_level)

theorem normalized_921 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3576 (c0_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) := (not_congr (normalization_3570 c0_depth r1_level))

theorem normalization_3577 (c0_depth r1_level : Int) : (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_3572 c0_depth r1_level))

theorem normalization_3578 (c0_depth r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) := (or_congr (normalization_3576 c0_depth r1_level) (normalization_3577 c0_depth r1_level))

theorem normalization_3579 (c0_depth r1_level : Int) : (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) := (not_congr (normalization_3578 c0_depth r1_level))

abbrev shared_expr_Repair039_35 (c0_depth r1_level : Int) : Prop := ((((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))))
theorem normalization_3580 (c0_depth r1_level : Int) : (formula_973 c0_depth r1_level) ↔ (shared_expr_Repair039_35 c0_depth r1_level) := (iff_congr (normalization_3574 c0_depth r1_level) (normalization_3579 c0_depth r1_level))

-- Checked replay of rewrite.
theorem replay_2411 (c0_depth r1_level : Int) : (formula_973 c0_depth r1_level) := by
  classical
  have ht := (normalized_921 ((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3580 c0_depth r1_level) hn

theorem normalized_922 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3581 (c0_depth r1_level : Int) : (((c0_depth ≤ r1_level) ∧ (c0_depth ≥ r1_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Repair039_35 c0_depth r1_level) := (iff_congr (normalization_3568 c0_depth r1_level) (normalization_3579 c0_depth r1_level))

-- Checked replay of trans.
theorem replay_2412 (c0_depth r1_level : Int) : (((c0_depth ≤ r1_level) ∧ (c0_depth ≥ r1_level)) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_922 (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) (shared_expr_Repair039_35 c0_depth r1_level))
  have n0 : (shared_expr_Repair039_33 c0_depth r1_level) := by
    exact Iff.mp (normalization_3575 c0_depth r1_level) (replay_2410 c0_depth r1_level)
  have n1 : (shared_expr_Repair039_35 c0_depth r1_level) := by
    exact Iff.mp (normalization_3580 c0_depth r1_level) (replay_2411 c0_depth r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3581 c0_depth r1_level) hn

theorem normalized_923 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3582 (c0_depth r1_level : Int) : ((c0_depth = r1_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))))) ↔ (shared_expr_Repair039_35 c0_depth r1_level) := (iff_congr (normalization_3235 c0_depth r1_level) (normalization_3579 c0_depth r1_level))

-- Checked replay of trans.
theorem replay_2413 (c0_depth r1_level : Int) : ((c0_depth = r1_level) ↔ (¬ ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))))) := by
  classical
  have ht := (normalized_923 (((c0_depth + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) (shared_expr_Repair039_35 c0_depth r1_level))
  have n0 : (shared_expr_Repair039_33 c0_depth r1_level) := by
    exact Iff.mp (normalization_3569 c0_depth r1_level) (replay_2407 c0_depth r1_level)
  have n1 : (shared_expr_Repair039_35 c0_depth r1_level) := by
    exact Iff.mp (normalization_3581 c0_depth r1_level) (replay_2412 c0_depth r1_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3582 c0_depth r1_level) hn

theorem normalized_924 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3583 (c0_node : Int) : ((c0_node % (2 : Int)) ≥ (0 : Int)) ↔ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3584 (c0_node : Int) : (((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (and_congr (normalization_508 c0_node) (normalization_3583 c0_node))

abbrev shared_expr_Repair039_36 (c0_node : Int) : Prop := (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3585 (c0_node : Int) : (((c0_node % (2 : Int)) = (0 : Int)) ↔ (((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (0 : Int)))) ↔ (shared_expr_Repair039_36 c0_node) := (iff_congr (normalization_159 c0_node) (normalization_3584 c0_node))

-- Checked replay of rewrite.
theorem replay_2414 (c0_node : Int) : (((c0_node % (2 : Int)) = (0 : Int)) ↔ (((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_924 ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3585 c0_node) hn

-- Checked replay of rewrite.
theorem replay_2415 (c0_node : Int) : (((c0_node % (2 : Int)) ≥ (0 : Int)) ↔ True) := by
  classical
  first | omega | grind (splits := 40)

theorem normalized_925 (p0 p1 : Prop) : (((p0 ↔ True)) → (((¬ p1) ∧ p0) ↔ ((¬ p1) ∧ True))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3586 (c0_node : Int) : (((c0_node % (2 : Int)) ≥ (0 : Int)) ↔ True) ↔ (((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) ↔ True) := (iff_congr (normalization_3583 c0_node) (normalization_305))

theorem normalization_3587 (c0_node : Int) : (((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ True) := (and_congr (normalization_508 c0_node) (normalization_305))

abbrev shared_expr_Repair039_37 (c0_node : Int) : Prop := (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ True))
theorem normalization_3588 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (0 : Int))) ↔ (((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ True)) ↔ (shared_expr_Repair039_37 c0_node) := (iff_congr (normalization_3584 c0_node) (normalization_3587 c0_node))

-- Checked replay of monotonicity.
theorem replay_2416 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (0 : Int))) ↔ (((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ True)) := by
  classical
  have ht := (normalized_925 ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have n0 : (((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) ↔ True) := by
    exact Iff.mp (normalization_3586 c0_node) (replay_2415 c0_node)
  have hn := ht n0
  exact Iff.mpr (normalization_3588 c0_node) hn

theorem normalized_926 (p0 : Prop) : (((¬ p0) ∧ True) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3589 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((c0_node % (2 : Int)) ≤ (0 : Int))) ↔ (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ True) ↔ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_3587 c0_node) (normalization_508 c0_node))

-- Checked replay of rewrite.
theorem replay_2417 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ True) ↔ ((c0_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_926 ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3589 c0_node) hn

theorem normalized_927 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair039_38 (c0_node : Int) : Prop := (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))))
theorem normalization_3590 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (0 : Int))) ↔ ((c0_node % (2 : Int)) ≤ (0 : Int))) ↔ (shared_expr_Repair039_38 c0_node) := (iff_congr (normalization_3584 c0_node) (normalization_508 c0_node))

-- Checked replay of trans.
theorem replay_2418 (c0_node : Int) : ((((c0_node % (2 : Int)) ≤ (0 : Int)) ∧ ((c0_node % (2 : Int)) ≥ (0 : Int))) ↔ ((c0_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_927 ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ True) ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair039_37 c0_node) := by
    exact Iff.mp (normalization_3588 c0_node) (replay_2416 c0_node)
  have n1 : (((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ True) ↔ (¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3589 c0_node) (replay_2417 c0_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3590 c0_node) hn

theorem normalized_928 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3591 (c0_node : Int) : (((c0_node % (2 : Int)) = (0 : Int)) ↔ ((c0_node % (2 : Int)) ≤ (0 : Int))) ↔ (shared_expr_Repair039_38 c0_node) := (iff_congr (normalization_159 c0_node) (normalization_508 c0_node))

-- Checked replay of trans.
theorem replay_2419 (c0_node : Int) : (((c0_node % (2 : Int)) = (0 : Int)) ↔ ((c0_node % (2 : Int)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_928 ((¬ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c0_node / (2 : Int))) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) (shared_expr_Repair039_38 c0_node))
  have n0 : (shared_expr_Repair039_36 c0_node) := by
    exact Iff.mp (normalization_3585 c0_node) (replay_2414 c0_node)
  have n1 : (shared_expr_Repair039_38 c0_node) := by
    exact Iff.mp (normalization_3590 c0_node) (replay_2418 c0_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3591 c0_node) hn

end H4Formal.Generated.Repair
